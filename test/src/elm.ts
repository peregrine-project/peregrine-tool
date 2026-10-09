import path from "path";
import { ExecResult, SimpleType, TestCase } from "./types";
import { appendFileSync, copyFileSync, existsSync, mkdirSync, readFileSync } from "fs";
import { execSync } from "child_process";
import { find_entry_point } from "./utils";

// Create a cargo.toml file and set up src/bin directory
export function prepare_elm_project(tmpdir: string): string {
  // Create directories
  let testdir = path.join(tmpdir, "elm/tests");
  if (!existsSync(testdir)) mkdirSync(testdir, { recursive: true });

  // Copy elm project definition
  copyFileSync("src/elm/elm.json", path.join(tmpdir, "elm/elm.json"));

  return testdir;
}

// Add main and test functions to `file` that calls `main_fn` and
// compares the return value to the expected output
function append_main(file: string, test: TestCase) {
  const main = find_entry_point(readFileSync(file, "utf8"), test.main);
  const content = (test.output_type == SimpleType.Other) ?
    `
main = Html.text (Debug.toString ${main})
test = let x = ${main} in Test.test "${main} test" (\ _ -> Expect.equal 1 1)
` : `
main = Html.text (Debug.toString ${main})
test = Test.test "${main} test" (\\ _ -> Expect.equal (Debug.toString ${main}) ("${test.expected_output[2]}"))
`;

  appendFileSync(file, content);
}

export function run_elm(file: string, tmpdir: string, test: TestCase, timeout: number): ExecResult {
  // TODO use "--report json" arg
  const cmd = `npx elm-test ${path.relative(tmpdir, file)}`;

  try {
    // Add main function to file
    append_main(file, test);

    // Run elm-test
    const start_main = Date.now();
    execSync(cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    return { type: "success", time: time_main };
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }
    if (e.status == 2) {
      // TODO parse stdout to retreive reason
      return { type: "error", reason: "incorrect result", actual: "TODO", expected: test.expected_output[2] }
    }

    return { type: "error", reason: "runtime error", error: e }; // TODO
  }
}
