import { execSync } from "child_process";
import { ExecFailure, ProgramType, SimpleType, TestCase } from "./types";
import { exit } from "process";
import { print_line, replace_ext } from "./utils";
import path from "path";
import { writeFileSync } from "fs";


// Convert ProgramType to OCaml type
function get_ocaml_type(type: ProgramType): string {
  switch (type) {
    case SimpleType.Bool:
      return "Types.bool_";
    case SimpleType.Nat:
      return "Types.nat";
    case SimpleType.UInt63:
      // TODO
      return "'a";
    case SimpleType.Other:
      return "'a";
    default:
      switch (type.type) {
        case "list":
          var a_t = get_ocaml_type(type.a_t);
          return `${a_t} Types.list_`;
        case "option":
          var a_t = get_ocaml_type(type.a_t);
          return `${a_t} Types.option_`;
        case "prod":
          var a_t = get_ocaml_type(type.a_t);
          var b_t = get_ocaml_type(type.b_t);
          return `(${a_t}, ${b_t}) Types.prod_`;
        default:
          break;
      }
      break;
  }
}

// Get OCaml printing function for a type
function get_pp_fun(type: ProgramType): string {
  switch (type) {
    case SimpleType.Bool:
      return "Types.pp_bool";
    case SimpleType.Nat:
      return "Types.pp_nat";
    case SimpleType.UInt63:
      // TODO
      return "";
    case SimpleType.Other:
      return "";
    default:
      switch (type.type) {
        case "list":
          var pp_a = get_pp_fun(type.a_t);
          return `Types.pp_list (${pp_a})`;
        case "option":
          var pp_a = get_pp_fun(type.a_t);
          return `Types.pp_option (${pp_a})`;
        case "prod":
          var pp_a = get_pp_fun(type.a_t);
          var pp_b = get_pp_fun(type.b_t);
          return `Types.pp_prod (${pp_a}) (${pp_b})`;
        default:
          break;
      }
      break;
  }
}

// Generate .mli file
function gen_mli(file: string, type: ProgramType) {
  const type_s = get_ocaml_type(type);
  const content = `val main : ${type_s}\n`;

  writeFileSync(file, content);
}

// Generate main wrapper
function gen_main(file: string, module: string, type: ProgramType) {
  const pp_fun = get_pp_fun(type);
  const pp = pp_fun.length > 0 ? `${pp_fun} x;\n  print_string "\\n"` : "()";
  const content =
    `open Printf

let go () =
  ${module.charAt(0).toUpperCase() + module.slice(1)}.main

let main =
  let x = go () in
  ${pp}
`;

  writeFileSync(file, content);
}

const util_dir = path.join(process.cwd(), "src/ocaml/");
const f_types = path.join(util_dir, "types.cmx");

// Compile .mlf file to OCaml executable
export function compile_ocaml(file: string, test: TestCase, timeout: number, tmpdir: string): string | ExecFailure {
  const f_mli = replace_ext(file, ".mli");
  const f_cmx = replace_ext(file, ".cmx");
  const f_main = path.join(path.dirname(file), path.basename(file, ".mlf") + "_main.ml");
  const f_main_cmx = replace_ext(f_main, ".cmx");
  const f_exec = replace_ext(f_main, "");

  const mli_cmd = `ocamlopt -I ${util_dir} -c ${f_mli}`;
  const mlf_cmd = `malfunction cmx ${file}`;
  const main_cmd = `ocamlopt -I ${util_dir} -c ${f_main}`;
  const exec_cmd = `ocamlopt -o ${f_exec} ${f_cmx} ${f_types} ${f_main_cmx}`;

  try {
    // Generate mli
    gen_mli(f_mli, test.output_type);

    // Generate main
    gen_main(f_main, path.basename(file, ".mlf"), test.output_type);

    // Compile program
    execSync(mli_cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });
    execSync(mlf_cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    // Compile main
    execSync(main_cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });
    execSync(exec_cmd, { stdio: "pipe", timeout: timeout, cwd: tmpdir });

    return f_exec;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "ocamlopt", code: e.status, error: e.stderr.toString('utf8') };
  }
}

// Compile `src/ocaml/types.ml`
export function compile_types(timeout) {
  try {
    execSync("ocamlopt -c src/ocaml/types.mli", { stdio: "pipe", timeout: timeout });
    execSync("ocamlopt -I src/ocaml/ -c src/ocaml/types.ml", { stdio: "pipe", timeout: timeout });

  } catch (e) {
    print_line("error: could not compile type definitions");
    print_line(e);
    exit(1);
  }
}
