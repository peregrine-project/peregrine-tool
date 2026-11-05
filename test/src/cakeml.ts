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
type CtorNames = (type: RegExp, ...names: string[]) => string;

// The constructors declared by the CakeML program `prog`: the backend names them
// by the kername of the inductive (of the first one of its mutual block), its
// index in its block, the constructor index and the constructor name. The
// constructor must belong to a type whose name matches `type`, as types of
// other shapes have constructors of the same names (Mutual's Even has zero and
// succ). The short names are those of the frontends: Rocq, Agda (∷ is
// __UU002237_, :: __UU3a_UU3a_, [] _UU5b_UU5d) and Lean (Nat.zero is
// Nat__UU2ezero).
function declared_ctors(prog: string): CtorNames {
  return (type, ...names) => {
    for (const name of names) {
      for (const m of prog.matchAll(new RegExp(`"(?:[^"]*\\.)?([^".]*)\\.\\d+\\.\\d+\\.${name}"`, "g"))) {
        if (type.test(m[1])) return m[0].slice(1, -1);
      }
    }
    throw new Error(`no constructor ${names.join(" or ")} of a type ${type} is declared in the CakeML program`);
  };
}

function get_printer(type: ProgramType, ctor: CtorNames, id: number = 0): { binds: string[], name: string } | undefined {
  const name = `pp${id}`;
  const arg = `(Var (Short "x"))`;
  const self = (v: string) => `(App Opapp ((Var (Short "${name}")) (Var (Short "${v}"))))`;
  switch (type) {
    case SimpleType.Nat: {
      const nat = /nat/i;
      const s = branch(ctor(nat, "S", "suc", "succ", "Nat__UU2esuc"), ["n"], seq(print_str("(S "), seq(self("n"), print_str(")"))));
      const body = `Mat ${arg} (${branch(ctor(nat, "O", "zero", "Nat__UU2ezero"), [], print_str("O"))} ${s})`;
      return { binds: [`(Dlet (unk unk) "${name}" (Letrec (("${name}" "x" ${body})) (Var (Short "${name}"))))`], name };
    }
    case SimpleType.Bool: {
      const bool = /bool/i;
      const body = `Mat ${arg} (${branch(ctor(bool, "true", "Bool__UU2etrue"), [], print_str("true"))} ${branch(ctor(bool, "false", "Bool__UU2efalse"), [], print_str("false"))})`;
      return { binds: [`(Dlet (unk unk) "${name}" (Fun "x" (${body})))`], name };
    }
    case SimpleType.UInt63:
      return undefined;
    default: {
      if (type.type !== "list") return undefined;
      const elem = get_printer(type.a_t, ctor, id + 1);
      if (elem === undefined) return undefined;
      const head = `(App Opapp ((Var (Short "${elem.name}")) (Var (Short "h"))))`;
      const list = /list|vec/i;
      const cons = branch(ctor(list, "cons", "__UU002237_", "__UU3a_UU3a_", "List__UU2econs"), ["h", "t"],
        seq(print_str("(cons "), seq(head, seq(print_str(" "), seq(self("t"), print_str(")"))))));
      const body = `Mat ${arg} (${branch(ctor(list, "nil", "empty", "_UU5b_UU5d", "List__UU2enil", "List__UU2eempty"), [], print_str("nil"))} ${cons})`;
      return {
        binds: [...elem.binds, `(Dlet (unk unk) "${name}" (Letrec (("${name}" "x" ${body})) (Var (Short "${name}"))))`],
        name
      };
    }
  }
}

// Append to the CakeML program in `file` the declarations printing `main`.
// The program is a single list of declarations.
function append_printer(file: string, type: ProgramType) {
  const prog = readFileSync(file, "utf8").trimEnd();
  const printer = get_printer(type, declared_ctors(prog));
  if (printer === undefined) throw new Error(`no CakeML printer for the type of the result`);
  const call = `(Dlet (unk unk) "pp_result" (App Opapp ((Var (Short "${printer.name}")) (Var (Short "main")))))`;
  if (!prog.endsWith(")")) throw new Error(`unexpected CakeML output in ${file}`);
  writeFileSync(file, `${prog.slice(0, -1)} ${printer.binds.join(" ")} ${call})\n`);
}

export function compile_cakeml(file: string, test: TestCase, timeout: number, tmpdir: string): string | ExecFailure {
  const f_cake = replace_ext(file, ".cake");

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

    append_printer(file, test.output_type);

    // Compile program. The printer uses TextIO from the prelude.
    execSync(`make -C ${path.join(tmpdir, cake_dir)} CAKEFLAGS="--sexp=true --skip_type_inference=true" ${f_cake}`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    return f_cake;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "cake", code: e.status, error: e.stderr?.toString('utf8') ?? `${e}` };
  }
}
