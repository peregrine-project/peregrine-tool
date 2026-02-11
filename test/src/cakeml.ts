import { execSync } from "child_process";
import { ExecFailure, ProgramType, SimpleType, TestCase } from "./types";
import { exit } from "process";
import { print_line, replace_ext } from "./utils";
import path from "path";
import { writeFileSync, existsSync } from "fs";



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


export function compile_cakeml(file: string, test: TestCase, timeout: number, tmpdir: string): string | ExecFailure {
  const f_cake = replace_ext(file, ".cake");

  try {
    // Patch names
    execSync(`sed -i.tmp 's/Ֆ/f/g' ${file}`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    // Compile program
    execSync(`make -C ${path.join(tmpdir, cake_dir)} CAKEFLAGS="--sexp=true --exclude_prelude=true --skip_type_inference=true" ${f_cake}`, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    return f_cake;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "cake", code: e.status, error: e.stderr.toString('utf8') };
  }
}
