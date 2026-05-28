import { execSync } from "child_process";
import { ExecResult, ProgramType, SimpleType, TestCase } from "./types";
import { appendFileSync, copyFileSync, cpSync, existsSync, mkdirSync } from "fs";
import path from "path";

const template_dir = path.join(process.cwd(), "src/lean/");
const runtime_src = path.join(process.cwd(), "..", "lean", "Peregrine", "Runtime.lean");

// Set up a fresh Lake project in tmpdir that the Lean test driver
// can build & run generated programs against.  Mirrors prepare_cargo
// / prepare_elm_project.  Returns the project root directory.
export function prepare_lean_project(tmpdir: string, timeout: number): string {
  const projectdir = path.join(tmpdir, "lean/");
  if (!existsSync(projectdir)) mkdirSync(projectdir, { recursive: true });

  // Copy static template files (lakefile.toml, lean-toolchain).
  cpSync(template_dir, projectdir, { recursive: true });

  // Pull the live Runtime from the repo root so we always test the
  // current backend's runtime support, not a snapshot.
  const runtime_dst_dir = path.join(projectdir, "Peregrine");
  if (!existsSync(runtime_dst_dir)) mkdirSync(runtime_dst_dir, { recursive: true });
  copyFileSync(runtime_src, path.join(runtime_dst_dir, "Runtime.lean"));

  // Warm the Lake cache so per-test runs don't each rebuild Runtime.
  execSync("lake build Peregrine", { stdio: "pipe", timeout: timeout, cwd: projectdir });

  return projectdir;
}

// Source-language inductive names used by the printers below.  These
// match the convention the existing lean_tests / agda / rocq programs
// follow (Bool_, Nat_, List_); each becomes `<Name>__` after the
// Lean backend's sanitiser + suffix pass (see lean/HANDOFF.md).
function pp_helpers(type: ProgramType): string {
  // Collect every helper the test's output_type transitively needs.
  const need = { bool: false, nat: false, list: false, option: false, prod: false };
  const visit = (t: ProgramType) => {
    if (t === SimpleType.Bool) need.bool = true;
    else if (t === SimpleType.Nat) need.nat = true;
    else if (typeof t !== "number") {
      if (t.type === "list") { need.list = true; visit(t.a_t); }
      else if (t.type === "option") { need.option = true; visit(t.a_t); }
      else if (t.type === "prod") { need.prod = true; visit(t.a_t); visit(t.b_t); }
    }
  };
  visit(type);

  const parts: string[] = [];
  if (need.bool) {
    parts.push(`unsafe def pp_bool (o : Obj) : String :=
  match (Peregrine.cast o : Generated.Bool__) with
  | .Bool__UU2efalse_ => "false"
  | .Bool__UU2etrue_ => "true"`);
  }
  if (need.nat) {
    parts.push(`unsafe def pp_nat (o : Obj) : String :=
  match (Peregrine.cast o : Generated.Nat__) with
  | .Nat__UU2ezero_ => "O"
  | .Nat__UU2esuc_ n => "(S " ++ pp_nat n ++ ")"`);
  }
  if (need.list) {
    parts.push(`unsafe def pp_list (ppA : Obj -> String) (o : Obj) : String :=
  match (Peregrine.cast o : Generated.List__) with
  | .List__UU2eempty_ => "nil"
  | .List__UU2econs_ h t => "(cons " ++ ppA h ++ " " ++ pp_list ppA t ++ ")"`);
  }
  if (need.option) {
    parts.push(`unsafe def pp_option (ppA : Obj -> String) (o : Obj) : String :=
  match (Peregrine.cast o : Generated.Option__) with
  | .Option__UU2eNone_ => "None"
  | .Option__UU2eSome_ x => "(Some " ++ ppA x ++ ")"`);
  }
  if (need.prod) {
    parts.push(`unsafe def pp_prod (ppA : Obj -> String) (ppB : Obj -> String) (o : Obj) : String :=
  match (Peregrine.cast o : Generated.Prod__) with
  | .Prod__UU2epair_ a b => "(pair " ++ ppA a ++ " " ++ ppB b ++ ")"`);
  }
  return parts.join("\n\n");
}

// Build the expression that prints a value of `type`.
function pp_call(type: ProgramType): string | undefined {
  if (type === SimpleType.Bool) return "pp_bool";
  if (type === SimpleType.Nat) return "pp_nat";
  if (type === SimpleType.UInt63) return undefined;
  if (type === SimpleType.Other) return undefined;
  if (typeof type === "number") return undefined;
  switch (type.type) {
    case "list": {
      const a = pp_call(type.a_t);
      return a === undefined ? undefined : `(pp_list ${a})`;
    }
    case "option": {
      const a = pp_call(type.a_t);
      return a === undefined ? undefined : `(pp_option ${a})`;
    }
    case "prod": {
      const a = pp_call(type.a_t);
      const b = pp_call(type.b_t);
      return (a && b) ? `(pp_prod ${a} ${b})` : undefined;
    }
  }
}

// Append a `main` to the generated file that prints the test's
// entry-point value using the s-expression format the existing
// expected_output[0] strings encode.
function append_main(file: string, test: TestCase) {
  const helpers = pp_helpers(test.output_type);
  const printer = pp_call(test.output_type);
  const target = `Generated.${test.main}`;

  const main_body = printer === undefined
    ? `let _ := ${target}; pure ()`
    : `IO.println (${printer} ${target})`;

  const content = `
${helpers}

unsafe def main : IO Unit :=
  ${main_body}
`;

  appendFileSync(file, content);
}

export function run_lean(file: string, projectdir: string, test: TestCase, timeout: number): ExecResult {
  try {
    append_main(file, test);

    const rel = path.relative(projectdir, file);
    const start_main = Date.now();
    // -Dlinter.unusedVariables=false: silence linter warnings the
    // generated code triggers (unused inductive parameters, erased
    // type arguments), which would otherwise pollute stdout.
    const res = execSync(`lake env lean -Dlinter.unusedVariables=false --run ${rel}`, {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
    }).trim();
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    if (test.expected_output === undefined || test.output_type === SimpleType.Other) {
      return { type: "success", time: time_main };
    }

    if (res !== test.expected_output[0]) {
      return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[0] };
    }

    return { type: "success", time: time_main };
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    const stderr = e.stderr ? e.stderr.toString("utf8") : "";
    const stdout = e.stdout ? e.stdout.toString("utf8") : "";
    return { type: "error", reason: "compile error", compiler: "lake", code: e.status, error: stderr || stdout };
  }
}
