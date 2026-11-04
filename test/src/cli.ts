import { spawnSync } from "child_process";
import path from "path";
import { writeFileSync } from "fs";
import { print_line } from "./utils";

// Checks of the frontend selection of the command line, which need none of
// the frontend tools: each command must fail with the exit code and the
// message that show which frontend peregrine chose for the input.
// [args, exit code, part of the error message]
const cli_tests: [string[], number, string][] = [
    [["c", "x.v"], 32, "a Rocq input needs --entry"],
    [["c", "x.lean"], 32, "a Lean input needs --entry"],
    [["c", "x.agda", "--entry", "f"], 32, "agda2lambox has no option to select a definition"],
    [["c", "x.lagda.md", "--entry", "f"], 32, "agda2lambox has no option to select a definition"],
    [["c", "x.ast", "--entry", "f"], 32, "apply to a proof-assistant source"],
    [["c", "x.v", "--from", "lambdabox"], 1, "Failed parsing input program"],
    [["c", "x.ast", "--from", "lean"], 32, "a Lean input needs --entry"],
    [["erase", "x.ast"], 32, "is a lambda box program already"],
    [["erase", "x.lean", "--entry", "f", "--typed"], 32, "the Lean frontend has no typed output"],
    [["rust", "x.lean", "--entry", "f"], 32, "is in no Lake project"],
];

// Run the checks with the peregrine binary `exec`, in `dir`, and return the
// failed ones
export function run_cli_tests(exec: string, dir: string): string[] {
    const failed: string[] = [];
    for (const f of ["x.v", "x.lean", "x.agda", "x.lagda.md", "x.ast"]) {
        writeFileSync(path.join(dir, f), "");
    }
    const check = (args: string[], code: number, msg: string, env?: NodeJS.ProcessEnv) => {
        const name = `peregrine ${args.join(" ")}`;
        process.stdout.write(`  ${name}: `);
        const r = spawnSync(exec, args, { cwd: dir, env: env ?? process.env, encoding: "utf8" });
        const out = (r.stdout ?? "") + (r.stderr ?? "");
        if (r.status === code && out.includes(msg)) {
            print_line("ok");
        } else {
            print_line(`expected exit code ${code} and "${msg}", got ${r.status}: ${out.trim()}`);
            failed.push(name);
        }
    };
    for (const [args, code, msg] of cli_tests) check(args, code, msg);
    // Frontend tools that are not on the PATH, which here has no programs
    const no_tools = { ...process.env, PATH: dir };
    check(["c", "x.agda"], 30, "agda2lambox not found", no_tools);
    check(["c", "x.lean", "--from", "rocq", "--entry", "f"], 30, "rocq not found", no_tools);
    return failed;
}
