// Test driver for the Koka backend (experimental).
import { execSync } from "child_process";
import { readFileSync, writeFileSync } from "fs";
import path from "path";
import { ExecFailure, ExecResult, ProgramType, SimpleType, TestCase } from "./types";

// The Koka tests need the koka compiler; without it they fail.
export function has_koka(): boolean {
  try {
    execSync("koka --version", { stdio: "pipe" });
    return true;
  } catch (e) {
    return false;
  }
}

// The constructors of the program's types: for each `type t { C1; C2( f0 : any ) }`
// the type name and, per constructor, its name and number of fields. The printer
// names a constructor `C_<type>_<index>_<source name>`.
type KokaType = { name: string, ctors: { name: string, short: string, nargs: number }[] };

function program_types(source: string): KokaType[] {
  const types: KokaType[] = [];
  for (const m of source.matchAll(/^type (t_\w+) \{ (.*) \}$/gm)) {
    const ctors = m[2].split("; ").filter((c) => c.length > 0).map((c) => {
      const name = c.split("(")[0].trim();
      // Lean's names keep the type: List.cons is List__UU2econs
      const short = name.replace(/^C_.*?_\d+_/, "").replace(/^.*__UU2e/, "");
      const nargs = c.includes("(") ? c.split(",").length : 0;
      return { name, short, nargs };
    });
    types.push({ name: m[1], ctors });
  }
  return types;
}

// The type whose constructors have the given source names (any of the
// alternatives at each position) and arities, in this order.
function find_type(types: KokaType[], shape: [string[], number][]): KokaType | undefined {
  return types.find((t) => t.ctors.length === shape.length
    && t.ctors.every((c, i) => shape[i][0].includes(c.short) && c.nargs === shape[i][1]));
}

// A Koka function `pp<id>` printing a value of `type` in the format of the
// expected outputs, with the declarations it needs, or undefined when the
// program declares no matching type.
function printer(types: KokaType[], type: ProgramType, id: number = 0): { decls: string[], name: string } | undefined {
  const name = `pp${id}`;
  const cast = (t: KokaType) => `(pg_cast(x) : ${t.name})`;
  if (type === SimpleType.Nat) {
    const t = find_type(types, [[["O", "zero"], 0], [["S", "succ", "suc"], 1]]);
    if (t === undefined) return undefined;
    const [z, s] = t.ctors;
    return { name, decls: [`fun ${name}( x : any ) : div string { match ${cast(t)} { ${z.name} -> "O"; ${s.name}(n) -> "(S " ++ ${name}(n) ++ ")" } }`] };
  }
  if (type === SimpleType.Bool) {
    const t = find_type(types, [[["true"], 0], [["false"], 0]]) ?? find_type(types, [[["false"], 0], [["true"], 0]]);
    if (t === undefined) return undefined;
    const br = t.ctors.map((c) => `${c.name} -> "${c.short}"`).join("; ");
    return { name, decls: [`fun ${name}( x : any ) : div string { match ${cast(t)} { ${br} } }`] };
  }
  if (typeof type === "number" || type.type !== "list") return undefined;
  const elem = printer(types, type.a_t, id + 1);
  // Agda's [] is _UU5b_UU5d, ∷ __UU002237_ and :: __UU3a_UU3a_
  const t = find_type(types, [[["nil", "empty", "_UU5b_UU5d"], 0], [["cons", "__UU002237_", "__UU3a_UU3a_"], 2]]);
  if (elem === undefined || t === undefined) return undefined;
  const [nil, cons] = t.ctors;
  return {
    name,
    decls: [...elem.decls, `fun ${name}( x : any ) : div string { match ${cast(t)} { ${nil.name} -> "nil"; ${cons.name}(h, t) -> "(cons " ++ ${elem.name}(h) ++ " " ++ ${name}(t) ++ ")" } }`]
  };
}

// Append a `main` that evaluates the test's entry point, and prints it when the
// output type has a printer, then compile the program. Returns the executable,
// and whether its output is checked.
export function compile_koka(file: string, test: TestCase, timeout: number): { exe: string, checked: boolean } | ExecFailure {
  const source = readFileSync(file, "utf8");
  const main = `pg_${test.main}`;
  const isDelayed = new RegExp(`^val ${main} : delayed`, "m").test(source);
  const target = isDelayed ? `pg_force(${main})` : main;
  const pp = printer(program_types(source), test.output_type);
  const body = pp === undefined
    ? `val pg_unused = unsafe-total(fn() { ${target} }); ()`
    : `println(${pp.name}(unsafe-total(fn() { ${target} })))`;
  // Koka derives the module name from the path, which must be a lower-case
  // identifier: the program is compiled as prog.kk in its own directory.
  const dir = path.dirname(file);
  writeFileSync(path.join(dir, "prog.kk"), `${source}\n${(pp?.decls ?? []).join("\n")}\npub fun main() { ${body} }\n`);

  const exe = path.join(dir, "prog");
  try {
    execSync(`koka -O2 -o prog prog.kk`, { stdio: "pipe", timeout: timeout, cwd: dir });
    execSync(`chmod +x ${exe}`, { stdio: "pipe" });
  } catch (e) {
    if (e.signal == "SIGTERM") return { type: "error", reason: "timeout" };
    const out = (e.stdout ? e.stdout.toString() : "") + (e.stderr ? e.stderr.toString() : "");
    const errors = out.split("\n").filter((l) => /error/.test(l));
    // The lines the errors point at, as the generated program is not kept.
    const lines = readFileSync(path.join(dir, "prog.kk"), "utf8").split("\n");
    const context = errors.flatMap((l) => {
      const m = l.match(/prog\.kk\((\d+),\s*(\d+)\)/);
      return m === null ? [] : [`  line ${m[1]}: ${lines[Number(m[1]) - 1].slice(Math.max(0, Number(m[2]) - 200), Number(m[2]) + 200)}`];
    });
    return { type: "error", reason: "compile error", compiler: "koka", code: e.status, error: [...errors, ...context].join("\n") || out.slice(-2000) };
  }
  return { exe, checked: pp !== undefined };
}

export function run_koka(exe: string, test: TestCase, checked: boolean, timeout: number): ExecResult {
  const start = Date.now();
  let res: string;
  try {
    res = execSync(`ulimit -s unlimited; ${exe}`, { stdio: "pipe", timeout: timeout, encoding: "utf8", shell: "/bin/bash" }).trim();
  } catch (e) {
    if (e.signal == "SIGTERM") return { type: "error", reason: "timeout" };
    return { type: "error", reason: "runtime error", error: e };
  }
  const time = Date.now() - start;
  if (!checked) {
    return { type: "error", reason: "incorrect result", actual: res, expected: "(no Koka printer: the program declares no type of the shape of the result)" };
  }
  if (res !== test.expected_output[0]) {
    return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[0] };
  }
  return { type: "success", time };
}
