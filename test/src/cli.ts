import { spawnSync } from "child_process";
import path from "path";
import { readFileSync, writeFileSync } from "fs";
import { print_line } from "./utils";

// Checks of the frontend selection of the command line, which need none of
// the frontend tools: each command must fail with the exit code and the
// message that show which frontend peregrine chose for the input. The checks
// of run_frontend_cli_tests below run the frontends that are installed.
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
    return failed.concat(run_frontend_cli_tests(exec, dir));
}

const has = (tool: string) => spawnSync("which", [tool]).status === 0;

// Checks that run the Rocq and Lean frontends, when they are installed:
// the load path and the logical path of a Rocq input, and --lean-config.
// Each erases a source to `out` and checks the messages of peregrine and the
// program it wrote.
function run_frontend_cli_tests(exec: string, dir: string): string[] {
    const failed: string[] = [];
    const erase = (name: string, cwd: string, args: string[], out: string,
                   msg: string, not_msg: string | undefined, ast: string) => {
        process.stdout.write(`  ${name}: `);
        const r = spawnSync(exec, ["erase", ...args, "-o", out], { cwd: cwd, encoding: "utf8" });
        const err = r.stderr ?? "";
        let content = "";
        try { content = readFileSync(out, "utf8"); } catch (e) { }
        if (r.status === 0 && err.includes(msg) && (not_msg === undefined || !err.includes(not_msg)) && content.includes(ast)) {
            print_line("ok");
        } else {
            print_line(`expected "${msg}"${not_msg ? ` without "${not_msg}"` : ""} and a program with ${ast}, got ${r.status}: ${err.trim()}`);
            failed.push(name);
        }
        return content;
    };
    if (has("rocq")) {
        // A project whose input requires another module, compiled first
        const proj = path.resolve("rocq-project");
        spawnSync("rocq", ["compile", "-Q", "theories", "Foo", "theories/Dep.v"], { cwd: proj });
        const lp = `(MPfile ("Main" "Sub" "Foo"))`;
        erase("Rocq project file", proj, ["theories/Sub/Main.v", "--entry", "main"], path.join(dir, "p1.ast"),
              "automatically detected Rocq project file", undefined, lp);
        erase("Rocq load path from --frontend-arg", proj,
              ["theories/Sub/Main.v", "--entry", "main", "--frontend-arg=-Q", "--frontend-arg=theories", "--frontend-arg=Foo"],
              path.join(dir, "p2.ast"), "extracting from Foo.Sub.Main", "Rocq project file", lp);
        writeFileSync(path.join(dir, "Alone.v"), "Definition x := 0.\n");
        erase("Rocq input in no load path", dir, ["Alone.v", "--entry", "x"], path.join(dir, "p3.ast"),
              "is in no load path", undefined, `(MPfile ("Alone"))`);
    } else {
        print_line("  error: rocq not found");
        failed.push("rocq");
    }
    if (has("lake")) {
        const two = ["lean/source/Two.lean", "--entry", "two"];
        const machine = erase("Lean, default configuration", ".", two, path.join(dir, "two.ast"),
                              "automatically detected Lake project", undefined, "primInt");
        const peano = erase("Lean, --lean-config", ".", [...two, "--lean-config", "{nat := .peano}"],
                            path.join(dir, "two_peano.ast"), "inlinings", undefined, `(inductive ((MPfile ()) "Nat") 0) 1`);
        if (peano.includes("primInt") || peano === machine) {
            print_line("  --lean-config: the program has machine integers still");
            failed.push("--lean-config");
        }
    } else {
        print_line("  error: lake not found");
        failed.push("lake");
    }
    return failed;
}
