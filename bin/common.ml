type verbose = Normal | Quiet | Verbose

(* The optional passes of the pipeline, as resolved from the command line
   (see [passes_t] in main.ml). [None] leaves the pass to the configuration
   file of `compile`, or else to the default pass set (if [optimize]), or
   else to the backend's default. *)
type passes = {
  (* The default pass set is on: false under -O0 *)
  optimize              : bool;
  inline_recursors      : bool;
  beta_reduce           : bool option;
  unbox                 : bool option;
  dearg_constants       : bool option;
  specialize_instances  : bool option;
  share_common_subterms : bool option;
  lift_constants        : bool option;
  (* Unverified lambda-box simplifications (ELboxOpts.v) *)
  unwrap_fixpoints      : bool;
  hoist_case_lambdas    : bool;
  drop_identity_matches : bool;
  inline_atomic_lets    : bool;
  (* Generalised iota reduction (ELboxOpts.v) *)
  iota_reduce           : bool;
  (* Automatic inlining (AutoInlining.v) *)
  inline_standard_constants : bool;
  inline_small_constants    : bool;
  inline_size_limit         : int;
  no_inline                 : string list;
}

type copts = {
  verbose: verbose;
  debug: bool;
  output_file: string option;
  attrs: string list;
  passes: passes;
  (* Fail instead of warning when the OCaml or CakeML backend's program is
     outside verified extraction's correctness theorem *)
  strict_verified: bool;
}
let mk_copts verbose debug output_file attrs passes strict_verified = {
  verbose;
  debug;
  output_file;
  attrs;
  passes;
  strict_verified;
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

type certirocq_opts = {
  cps: bool;
  c_args: int option;
  o_level: int option;
  body_name: string option;
}

let mk_certirocq_opts cps c_args o_level body_name = {
  cps;
  c_args;
  o_level;
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
