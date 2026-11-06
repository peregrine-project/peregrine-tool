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
// A typed program keeps a `()` field per type parameter in front of the source
// fields (`cons( f0 : (), f1 : a0, f2 : ... )`): `units` counts them, and `nargs`
// and `first` describe the source fields.
type KokaType = { name: string, base: string, ctors: { name: string, short: string, nargs: number, units: number, first?: string }[] };

function program_types(source: string): KokaType[] {
  const types: KokaType[] = [];
  for (const m of source.matchAll(/^type (t_\w+)(<([^>]*)>)? \{ (.*) \}$/gm)) {
    // a typed program's types have parameters; the printers read them as any
    const arity = m[3] === undefined ? 0 : m[3].split(",").length;
    const ctors = m[4].split("; ").filter((c) => c.length > 0).map((c) => {
      const name = c.split("(")[0].trim();
      // Lean's names keep the type: List.cons is List__UU2econs
      const short = name.replace(/^C_.*?_\d+_/, "").replace(/^.*__UU2e/, "");
      const inner = c.includes("(") ? c.slice(c.indexOf("(") + 1, c.lastIndexOf(")")) : "";
      const fields = inner.trim().length === 0 ? [] : inner.split(/,\s*(?=f\d+ : )/).map((f) => f.replace(/^\s*f\d+ : /, "").trim());
      const lead = fields.findIndex((t) => t !== "()");
      const units = arity === 0 ? 0 : (lead === -1 ? fields.length : lead);
      return { name, short, nargs: fields.length - units, units, first: fields[units] };
    });
    types.push({ name: arity === 0 ? m[1] : `${m[1]}<${Array(arity).fill("any").join(", ")}>`, base: m[1], ctors });
  }
  return types;
}

// The type whose constructors have the given source names (any of the
// alternatives at each position) and arities, in this order.
function find_types(types: KokaType[], shape: [string[], number][]): KokaType[] {
  return types.filter((t) => t.ctors.length === shape.length
    && t.ctors.every((c, i) => shape[i][0].includes(c.short) && c.nargs === shape[i][1]));
}
function find_type(types: KokaType[], shape: [string[], number][]): KokaType | undefined {
  return find_types(types, shape)[0];
}

// The pattern of constructor `c` binding its source fields to `vars`.
function pat(c: KokaType["ctors"][number], vars: string[]): string {
  const all = [...Array(c.units).fill("_"), ...vars];
  return all.length === 0 ? c.name : `${c.name}(${all.join(", ")})`;
}

// A Koka function `pp<id>` printing a value of `type` in the format of the
// expected outputs, with the declarations it needs, or undefined when the
// program declares no matching type.
function printer(types: KokaType[], type: ProgramType, id: number = 0): { decls: string[], name: string } | undefined {
  const name = `pp${id}`;
  const cast = (t: KokaType) => `(pg_cast(x) : ${t.name})`;
  if (type === SimpleType.Nat) {
    // a typed program may have other zero/succ-shaped types (Even with a
    // successor into Odd): prefer the one whose successor takes itself
    const ts = find_types(types, [[["O", "zero"], 0], [["S", "succ", "suc"], 1]]);
    const t = ts.find((u) => u.ctors[1].first === u.base) ?? ts[0];
    if (t === undefined) return undefined;
    const [z, s] = t.ctors;
    return { name, decls: [`fun ${name}( x : any ) : div string { match ${cast(t)} { ${pat(z, [])} -> "O"; ${pat(s, ["n"])} -> "(S " ++ ${name}(pg_cast(n)) ++ ")" } }`] };
  }
  if (type === SimpleType.Bool) {
    const t = find_type(types, [[["true"], 0], [["false"], 0]]) ?? find_type(types, [[["false"], 0], [["true"], 0]]);
    if (t === undefined) return undefined;
    const br = t.ctors.map((c) => `${pat(c, [])} -> "${c.short}"`).join("; ");
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
    decls: [...elem.decls, `fun ${name}( x : any ) : div string { match ${cast(t)} { ${pat(nil, [])} -> "nil"; ${pat(cons, ["h", "t"])} -> "(cons " ++ ${elem.name}(pg_cast(h)) ++ " " ++ ${name}(pg_cast(t)) ++ ")" } }`]
  };
}

// Append a `main` that evaluates the test's entry point, and prints it when the
// output type has a printer, then compile the program. Returns the executable,
// and whether its output is checked.
export function compile_koka(file: string, test: TestCase, timeout: number): { exe: string, checked: boolean } | ExecFailure {
  const source = readFileSync(file, "utf8");
  // The entry point: pg_<main>, or for the typed backend the full name ending in it
  // (a Lean name separates its components with "Ֆdot", which the sanitizer
  // escapes as _UU000556dot)
  const main_re = test.main.replace(/_/g, "(?:_|_UU[0-9a-f]{6}dot|_UU2e)");
  const found = source.match(new RegExp(`^(val|fun) (pg_\\w*?${main_re})\\b(\\(\\))?`, "m"));
  // failing that, a name ending in the last component of the entry point
  const last = test.main.split("_").pop();
  const fallback = found === null ? source.match(new RegExp(`^(val|fun) (pg_(?:\\w*_)?${last})\\b(\\(\\))?`, "m")) : null;
  const entry = found ?? fallback;
  if (entry === null) {
    const names = [...source.matchAll(/^(?:val|fun) (pg_\w+)/gm)].map((m) => m[1]);
    console.log(`  no entry point for ${test.main} among: ${names.slice(-8).join(" ")}`);
  }
  const main = entry === null ? `pg_${test.main}` : entry[2];
  const isDelayed = new RegExp(`^val ${main} : delayed`, "m").test(source);
  const isNullaryFun = entry !== null && entry[1] === "fun" && entry[3] !== undefined;
  const target = isDelayed ? `pg_force(${main})` : isNullaryFun ? `${main}()` : main;
  const pp = printer(program_types(source), test.output_type);
  // The printers cast with pg_cast, which only the untyped preamble declares
  const cast = source.includes("extern pg_cast") ? "" : `extern pg_cast( x : a ) : b { c inline "#1"; js inline "#1" }\n`;
  const body = pp === undefined
    ? `val pg_unused = unsafe-total(fn() { ${target} }); ()`
    : `println(${pp.name}(pg_cast(unsafe-total(fn() { ${target} }))))`;
  // Koka derives the module name from the path, which must be a lower-case
  // identifier: the program is compiled as prog.kk in its own directory.
  const dir = path.dirname(file);
  writeFileSync(path.join(dir, "prog.kk"), `${source}\n${cast}${(pp?.decls ?? []).join("\n")}\npub fun main() { ${body} }\n`);

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
    const out = (e.stderr ? e.stderr.toString() : "") || (e.stdout ? e.stdout.toString() : "");
    return { type: "error", reason: "runtime error", error: `status ${e.status}, signal ${e.signal}: ${out.slice(-2000)}` };
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
