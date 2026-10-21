// Test driver for the F# backend (experimental).
import { execSync } from "child_process";
import { ExecFailure, ExecResult, ProgramType, SimpleType, TestCase } from "./types";
import { cpSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import { exit } from "process";
import { print_line } from "./utils";
import path from "path";

const template_dir = path.join(process.cwd(), "src/fsharp/");

// Keep the SDK quiet and reproducible across machines.
const dotnet_env = { ...process.env, DOTNET_CLI_TELEMETRY_OPTOUT: "1", DOTNET_NOLOGO: "1" };

const build_cmd = "dotnet build -c Release --no-restore --nologo -v:q";

// Collect whatever a failed execSync captured, preferring stderr.
function exec_output(e): string {
  const stderr = e.stderr ? e.stderr.toString() : "";
  const stdout = e.stdout ? e.stdout.toString() : "";
  return stderr || stdout;
}

// The F# tests need the .NET SDK; without it they are skipped.
export function has_dotnet(): boolean {
  try {
    execSync("dotnet --version", { stdio: "pipe", env: dotnet_env });
    return true;
  } catch (e) {
    return false;
  }
}

// Set up a fresh .NET project in tmpdir that the F# test driver can
// build & run generated programs against.  Mirrors prepare_cargo /
// prepare_elm_project.  Returns the project root directory.
export function prepare_fsharp_project(tmpdir: string, timeout: number): string {
  const projectdir = path.join(tmpdir, "fsharp/");
  if (!existsSync(projectdir)) mkdirSync(projectdir, { recursive: true });

  // Copy static template files (fsharp_tests.fsproj, TestPrinters.fs,
  // and the stub Main.fs that build_fsharp overwrites).
  cpSync(template_dir, projectdir, { recursive: true });

  // Warm build: performs the one (offline, library-packs-backed) restore.
  // A cold SDK start (first-run setup + restore) is far slower than a
  // build, so this gets its own budget instead of the compile timeout.
  const warm_timeout = Math.max(timeout * 4, 120000);

  try {
    execSync("dotnet build -c Release --nologo -v:q", {
      stdio: "pipe",
      timeout: warm_timeout,
      cwd: projectdir,
      env: dotnet_env,
    });
  } catch (e) {
    // Like compile_types for the OCaml backend, a broken prepare phase is
    // fatal for the whole suite: report it readably instead of letting a
    // raw exception unwind out of main().
    print_line("error: could not prepare the F# test project");
    if (e.signal == "SIGTERM") {
      print_line(`dotnet build timed out after ${warm_timeout} ms`);
    } else {
      print_line(`dotnet build failed with code ${e.status}`);
    }
    print_line(exec_output(e));
    exit(1);
  }

  return projectdir;
}

// Build an F# expression that prints an extracted value of `type` via
// the universal printers in TestPrinters.  Those printers read union
// case tags and fields by reflection, so they match any source
// inductive with the same constructor arities in the same order —
// Bool false/then true, Nat zero/then succ, List nil/then cons — and
// therefore work regardless of which frontend produced the .ast
// (rocq, agda, lean, ...).
function pp_call(type: ProgramType): string | undefined {
  if (type === SimpleType.Bool) return "TestPrinters.pp_bool";
  if (type === SimpleType.Nat) return "TestPrinters.pp_nat";
  if (type === SimpleType.UInt63) return undefined;
  if (type === SimpleType.Other) return undefined;
  if (typeof type === "number") return undefined;
  switch (type.type) {
    case "list": {
      const a = pp_call(type.a_t);
      return a === undefined ? undefined : `(TestPrinters.pp_list ${a})`;
    }
    case "option":
    case "prod":
      // No universal printers for these yet; treat as opaque so the
      // runner just exercises evaluation without checking the result.
      return undefined;
  }
}

// One generated program of the batch: the test and the file peregrine wrote.
export type FSharpProgram = { test: TestCase, file: string };

// Module name of the i-th program of the batch.
const module_name = (i: number) => `T${i}`;

// Copy the i-th program into the project under its own module name, so that
// all the programs compile together, and return the dispatch case that
// evaluates (and, when there is a printer, prints) its entry point.
// Nullary constants are emitted as Lazy<obj> and must be forced inside the
// big-stack thread, never at module init on the 1 MiB stack.
function add_program(projectdir: string, i: number, p: FSharpProgram): string {
  const source = readFileSync(p.file, "utf8").replace(/^module \S+/, `module ${module_name(i)}`);
  writeFileSync(path.join(projectdir, `${module_name(i)}.fs`), source);

  const main = p.test.main;
  const isLazy = new RegExp(`let(?:\\s+rec)?\\s+${main}\\s*:\\s*Lazy<obj>`).test(source);
  const target = isLazy ? `${module_name(i)}.${main}.Force()` : `box ${module_name(i)}.${main}`;
  const printer = pp_call(p.test.output_type);
  const body = printer === undefined
    ? `ignore (${target})`
    : `System.Console.Out.WriteLine(${printer} (${target}))`;
  return `        | "${i}" -> ${body}`;
}

// Line of Main.fs that holds the dispatch case of the first program.
const main_first_case = 7;

// Write the project for the programs whose index is in `members` and build
// it. Returns undefined on success, or the build output.
function build_project(projectdir: string, cases: string[], members: number[], timeout: number): string | undefined {
  const compile = members.map((i) => `    <Compile Include="${module_name(i)}.fs" />`).join("\n");
  const fsproj = readFileSync(path.join(template_dir, "fsharp_tests.fsproj"), "utf8")
    .replace(`    <Compile Include="Main.fs" />`, `${compile}\n    <Compile Include="Main.fs" />`);
  writeFileSync(path.join(projectdir, "fsharp_tests.fsproj"), fsproj);

  writeFileSync(path.join(projectdir, "Main.fs"), `module Main

[<EntryPoint>]
let main (argv: string[]) =
    let run () =
        match argv.[0] with
${members.map((i) => cases[i]).join("\n")}
        | n -> failwithf "unknown test %s" n
    let t = System.Threading.Thread(run, 536870912)   // 512 MiB stack
    t.Start()
    t.Join()
    0
`);

  try {
    execSync(build_cmd, { stdio: "pipe", timeout: timeout, cwd: projectdir, encoding: "utf8", env: dotnet_env });
    return undefined;
  } catch (e) {
    if (e.signal == "SIGTERM") return "timeout";
    return exec_output(e);
  }
}

// Build all the programs as one executable, as one dotnet build per test
// would cost seconds each. A program that does not compile is removed and the
// rest is built again. Returns the failure of each program that did not build.
export function build_fsharp(projectdir: string, programs: FSharpProgram[], timeout: number): Map<number, ExecFailure> {
  const failures = new Map<number, ExecFailure>();
  const cases = programs.map((p, i) => add_program(projectdir, i, p));
  let members = programs.map((_, i) => i);

  // The whole batch gets the compile timeout of each of its programs.
  const batch_timeout = timeout * Math.max(1, programs.length);
  const err = build_project(projectdir, cases, members, batch_timeout);
  if (err === undefined) return failures;

  // Attribute the errors to the programs they are reported in: the file of
  // the program, or its dispatch case in Main.fs, whose first case is on
  // line main_first_case.
  const owner = (line: string): number | undefined => {
    const m = line.match(/\/(T(\d+)|Main)\.fs\((\d+),/);
    if (m === null) return undefined;
    return m[2] !== undefined ? Number(m[2]) : members[Number(m[3]) - main_first_case];
  };
  const errors = new Map<number, string[]>();
  for (const line of err.split("\n")) {
    const i = owner(line);
    if (i !== undefined) errors.set(i, [...(errors.get(i) ?? []), line]);
  }
  const failing = members.filter((i) => errors.has(i));
  for (const i of failing) {
    failures.set(i, { type: "error", reason: "compile error", compiler: "dotnet", code: 1, error: errors.get(i).join("\n") });
  }
  members = members.filter((i) => !failing.includes(i));

  const err2 = failing.length === 0 ? err : build_project(projectdir, cases, members, batch_timeout);
  if (err2 !== undefined) {
    for (const i of members) {
      failures.set(i, err2 === "timeout"
        ? { type: "error", reason: "timeout" }
        : { type: "error", reason: "compile error", compiler: "dotnet", code: 1, error: err2 });
    }
  }
  return failures;
}

// Run the i-th program of the batch built by build_fsharp.
export function run_fsharp(projectdir: string, i: number, test: TestCase, timeout: number): ExecResult {
  // When there is no printer for the output type the program prints
  // nothing, so the test is run-only: succeeding means it exited cleanly.
  const printer = pp_call(test.output_type);

  const start_main = Date.now();
  var res: string;
  try {
    res = execSync(`dotnet bin/Release/net10.0/testexe.dll ${i}`, {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
      env: dotnet_env,
    }).trim();
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "runtime error", error: exec_output(e) || `${e}` };
  }
  const time_main = Date.now() - start_main;

  // Return success if there is no expected output to compare against, if the
  // program returns a type that we don't know how to print, or if we have no
  // printer for it (nothing was written to stdout in that case).
  if (test.expected_output === undefined || test.output_type === SimpleType.Other || printer === undefined) {
    return { type: "success", time: time_main };
  }

  // Compare output against the expected output
  if (res !== test.expected_output[0]) {
    return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[0] };
  }

  return { type: "success", time: time_main };
}
