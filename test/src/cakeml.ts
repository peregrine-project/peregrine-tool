import { execSync } from "child_process";
import { ExecFailure, ProgramType, SimpleType, TestCase } from "./types";
import { exit } from "process";
import { print_line, replace_ext } from "./utils";
import path from "path";
import { readFileSync, writeFileSync, existsSync } from "fs";



function get_cakeml_url() {
  if (process.arch === "arm" || process.arch === "arm64") {
    return "https://github.com/CakeML/cakeml/releases/download/v3213/cake-arm8-64.tar.gz";
  } else {
    return "https://github.com/CakeML/cakeml/releases/download/v3213/cake-x64-64.tar.gz";
  }
}

function get_cakeml_dir() {
  if (process.arch === "arm" || process.arch === "arm64") {
    return "cake-arm8-64";
  } else {
    return "cake-x64-64";
  }
}

const url = get_cakeml_url();
const cake_dir = get_cakeml_dir();


export function get_cake(timeout: number, tmpdir: string) {
  if (existsSync(path.join(tmpdir, cake_dir))) {
    return; // CakeML is already installed
  }

  // Download cakeml
  execSync(`curl -L ${url} | tar zx`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });
}


// An expression printing the string `s`
function print_str(s: string): string {
  return `(App Opapp ((Var (Long "TextIO" (Short "print"))) (Lit "${s}")))`;
}

// The expression `e1; e2`
function seq(e1: string, e2: string): string {
  return `(Let NONE ${e1} ${e2})`;
}

// A match branch on constructor `ctor` with the fields `vars`
function branch(ctor: string, vars: string[], body: string): string {
  const pat = vars.length === 0 ? "nil" : `(${vars.map((v) => `"${v}"`).join(" ")})`;
  return `((Pcon (SOME (Short "${ctor}")) ${pat}) . ${body})`;
}

// A function printing a value of type `type`, in the format of the expected
// outputs. Returns the bindings it needs and its name, or undefined for a type
// that cannot be printed. It matches on constructors by the names the CakeML
// backend gives them, which `ctor` supplies given the short names to try.
// The cake compiler runs with type inference skipped and lets a pattern with an
// undeclared constructor match any value, so `ctor` must find the declared name.
type CtorNames = (...names: string[]) => string;

// The constructors declared by the CakeML program `prog`: the backend names them
// by the kername of the inductive, its index in its mutual block, the constructor
// index and the constructor name.
function declared_ctors(prog: string): CtorNames {
  return (...names) => {
    for (const name of names) {
      const m = prog.match(new RegExp(`"[^"]*\\.\\d+\\.\\d+\\.${name}"`));
      if (m !== null) return m[0].slice(1, -1);
    }
    throw new Error(`no constructor ${names.join(" or ")} is declared in the CakeML program`);
  };
}

function get_printer(type: ProgramType, ctor: CtorNames, id: number = 0): { binds: string[], name: string } | undefined {
  const name = `pp${id}`;
  const arg = `(Var (Short "x"))`;
  const self = (v: string) => `(App Opapp ((Var (Short "${name}")) (Var (Short "${v}"))))`;
  switch (type) {
    case SimpleType.Nat: {
      const s = branch(ctor("S"), ["n"], seq(print_str("(S "), seq(self("n"), print_str(")"))));
      const body = `Mat ${arg} (${branch(ctor("O"), [], print_str("O"))} ${s})`;
      return { binds: [`(Dlet (unk unk) "${name}" (Letrec (("${name}" "x" ${body})) (Var (Short "${name}"))))`], name };
    }
    case SimpleType.Bool: {
      const body = `Mat ${arg} (${branch(ctor("true"), [], print_str("true"))} ${branch(ctor("false"), [], print_str("false"))})`;
      return { binds: [`(Dlet (unk unk) "${name}" (Fun "x" (${body})))`], name };
    }
    case SimpleType.UInt63:
    case SimpleType.Other:
      return undefined;
    default: {
      if (type.type !== "list") return undefined;
      const elem = get_printer(type.a_t, ctor, id + 1);
      if (elem === undefined) return undefined;
      const head = `(App Opapp ((Var (Short "${elem.name}")) (Var (Short "h"))))`;
      const cons = branch(ctor("cons"), ["h", "t"],
        seq(print_str("(cons "), seq(head, seq(print_str(" "), seq(self("t"), print_str(")"))))));
      const body = `Mat ${arg} (${branch(ctor("nil", "empty"), [], print_str("nil"))} ${cons})`;
      return {
        binds: [...elem.binds, `(Dlet (unk unk) "${name}" (Letrec (("${name}" "x" ${body})) (Var (Short "${name}"))))`],
        name
      };
    }
  }
}

// Whether the output of `test` is compared with the expected one. Only tests
// extracted from Rocq are checked: other frontends use other constructor names.
export function cakeml_output_checked(test: TestCase): boolean {
  return test.expected_output !== undefined
    && test.src?.startsWith("rocq/") === true
    && get_printer(test.output_type, (name) => name) !== undefined;
}

// Append to the CakeML program in `file` the declarations printing `main`.
// The program is a single list of declarations.
function append_printer(file: string, type: ProgramType) {
  const prog = readFileSync(file, "utf8").trimEnd();
  const printer = get_printer(type, declared_ctors(prog))!;
  const call = `(Dlet (unk unk) "pp_result" (App Opapp ((Var (Short "${printer.name}")) (Var (Short "main")))))`;
  if (!prog.endsWith(")")) throw new Error(`unexpected CakeML output in ${file}`);
  writeFileSync(file, `${prog.slice(0, -1)} ${printer.binds.join(" ")} ${call})\n`);
}

export function compile_cakeml(file: string, test: TestCase, timeout: number, tmpdir: string): string | ExecFailure {
  const f_cake = replace_ext(file, ".cake");
  const checked = cakeml_output_checked(test);

  try {
    // Patch names
    execSync(`sed -i.tmp 's/Ֆ/f/g' ${file}`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });
    // Upstream CertiRocq CakeML extraction emits the tBox placeholder
    // for unresolvable mains as a malformed `(Dlet ... (Raise (Lit
    // Strlit "...")))`.  Two issues: the constructor name is wrong
    // ("Strlit" vs CakeML's "StrLit") and the parenthesisation puts
    // [Lit] and its argument at the same level.  We don't need the
    // placeholder anyway (the test backends that observe output
    // don't check it for these programs), so rewrite the whole
    // [Dlet] to a no-op unit binding.
    execSync(`sed -i 's|(Dlet (unk unk) "main" (Raise (Lit Strlit "[^"]*")))|(Dlet (unk unk) "main" (Con NONE nil))|g' ${file}`,
      { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    if (checked) append_printer(file, test.output_type);

    // Compile program. The printer uses TextIO from the prelude.
    const prelude = checked ? "" : " --exclude_prelude=true";
    execSync(`make -C ${path.join(tmpdir, cake_dir)} CAKEFLAGS="--sexp=true${prelude} --skip_type_inference=true" ${f_cake}`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    return f_cake;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "cake", code: e.status, error: e.stderr.toString('utf8') };
  }
}
