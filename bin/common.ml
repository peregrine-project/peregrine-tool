type verbose = Normal | Quiet | Verbose

type copts = {
  verbose: verbose;
  debug: bool;
  output_file: string option;
  attrs: string list;
  inline_recursors: bool;
}
let mk_copts verbose debug output_file attrs inline_recursors = {
  verbose;
  debug;
  output_file;
  attrs;
  inline_recursors
}

(* The frontends, see frontend.ml *)
type frontend = Rocq | Agda | Lean | LambdaBox

type frontend_opts = {
  from: frontend option;
  entry: string option;
  frontend_args: string list;
  keep_ast: string option;
  typed: bool;
  lean_config: string option;
}
let mk_frontend_opts from entry frontend_args keep_ast typed lean_config = {
  from;
  entry;
  frontend_args;
  keep_ast;
  typed;
  lean_config;
}

type erasure_opts = {
  betared             : bool option;
  unboxing            : bool option;
  dearg_ctors         : bool option;
  dearg_consts        : bool option;
  specialize_instances : bool option;
  cse                 : bool option;
  lower_cofix         : bool option;
}

let mk_erasure_opts betared unboxing dearg_ctors dearg_consts specialize_instances cse lower_cofix = {
  betared;
  unboxing;
  dearg_ctors;
  dearg_consts;
  specialize_instances;
  cse;
  lower_cofix;
}

type certirocq_opts = {
  cps: bool;
  c_args: int option;
  o_level: int option;
  anf_conf: int option;
  prefix: string option;
  body_name: string option;
}

let mk_certirocq_opts cps c_args o_level anf_conf prefix body_name = {
  cps;
  c_args;
  o_level;
  anf_conf;
  prefix;
  body_name;
}

type astType =
    Box
  | BoxTyped
  | ANF
  | ANFC

type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option

let read_file f =
  let c = open_in_bin f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  s
