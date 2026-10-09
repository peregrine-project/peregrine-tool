import path from "path";
import { ExecFailure, ExecResult, SimpleType, TestCase } from "./types";
import { appendFileSync, copyFileSync, existsSync, mkdirSync, readFileSync } from "fs";
import { execSync } from "child_process";
import { find_entry_point } from "./utils";

// Create a cargo.toml file and set up src/bin directory
export function prepare_cargo(tmpdir: string): string {
  // Create directories
  let dir = path.join(tmpdir, "rust/src/bin");
  if (!existsSync(dir)) mkdirSync(dir, { recursive: true });

  // Copy cargo project definition
  copyFileSync("src/rust/Cargo.toml", path.join(tmpdir, "rust/Cargo.toml"));

  return dir;
}


// Add main function to `file` that calls `main_fn` and
// prints the return value using s-expression printer
function append_main(file: string, test: TestCase) {
  const main = find_entry_point(readFileSync(file, "utf8"), test.main);
  const content = (test.output_type == SimpleType.Other) ?
    `fn main() {
  Program::new().${main}();
}
` : `fn main() {
  let y = to_value(Program::new().${main}());
  println!("{}", to_string(&y.unwrap()).unwrap())
}
`;

  appendFileSync(file, content);
}

export function compile_rust(file: string, tmpdir: string, test: TestCase, timeout: number): ExecFailure {
  const m = path.basename(file, ".rs");
  const cmd = `cargo build --bin ${m}`;

  try {
    // Add main function to file
    append_main(file, test);

    // Run carbo build
    execSync(cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    return undefined;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "cargo", code: e.status, error: e.stderr.toString('utf8') };
  }
}

export function run_rust(file: string, tmpdir: string, test: TestCase, timeout: number): ExecResult {
  // Command to run
  const m = path.basename(file, ".rs");
  const cmd = `cargo run -q --bin ${m}`;

  try {
    // Run and time the command
    const start_main = Date.now();
    const res = execSync(cmd, { stdio: "pipe", timeout: timeout, encoding: "utf8", cwd: tmpdir }).trim();
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    // Return success if there is no expected output to compare against or if the program
    // returns a type that we don't know how to print
    if (test.expected_output === undefined || test.output_type === SimpleType.Other) {
      return { type: "success", time: time_main };
    }

    // Compare output against the expected output
    if (res !== test.expected_output[1]) {
      return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[1] };
    }

    return { type: "success", time: time_main };
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "runtime error", error: e }; // TODO
  }

  // TODO
  return null;
}


/* TODO
* x Create rust/src/bin dir in TMPDIR
* x Move rust/Cargo.toml to TMPDIR/rust
* x Compile lambox to rs into rust/src/bin
  * x Set extra Serialize attribute
  * x Add extra imports to prelude
* [] Append main function
* [] Compile rust using `cargo build --bin NAME`
* [] Run using `cargo run -q --bin NAME`
*/
