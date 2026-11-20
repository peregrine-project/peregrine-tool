open Common
open Peregrine.Caml_bytestring

module Datatypes = Peregrine.Datatypes
module Config = Peregrine.Config0
module ConfigUtils = Peregrine.ConfigUtils
module RustGMPRemaps = Peregrine.RustGMPRemaps
module RustNativeRemaps = Peregrine.RustNativeRemaps
module RustMixedRemaps = Peregrine.RustMixedRemaps
module RustHybridRemaps = Peregrine.RustHybridRemaps
module Pipeline = Peregrine.Pipeline2
module PipelineParse = Peregrine.PipelineParse
module ResultMonad = Peregrine.ResultMonad
module Anf_term = Peregrine.Term0



(* String conversion *)
let string_of_cstring = Peregrine.Camlcoq.camlstring_of_coqstring
let cstring_of_string = Peregrine.Camlcoq.coqstring_of_camlstring

let cprint_endline s =
  print_endline (caml_string_of_bytestring s)



(* Extraction output helper functions. [stem] is the input file without its
   extension. *)
let get_out_file opts stem ext =
  match opts.output_file with
  | Some f -> f
  | None -> stem^"."^ext

let get_header_file opts stem =
  match opts.output_file with
  | Some f -> (Filename.remove_extension f)^".h"
  | None -> stem^".h"

let write_res f p =
  let f = open_out f in
  p f;
  flush f;
  close_out f

let write_wasm_res opts f p =
  let f = get_out_file opts f "wasm" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_llvm_res opts f p =
  let f = get_out_file opts f "ll" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_elm_res opts f p =
  let f = get_out_file opts f "elm" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_rust_res opts f p =
  let f = get_out_file opts f "rs" in
  write_res f (fun f ->
    List.iter (fun s -> output_string f ((caml_string_of_bytestring s) ^ "\n")) p)

let write_ocaml_res opts f p =
  let f = get_out_file opts f "mlf" in
  write_res f (fun f ->
    output_string f (caml_string_of_bytestring (snd p)))

let write_cakeml_res opts f p =
  let f = get_out_file opts f "cml" in
  write_res f (fun f ->
    output_string f (caml_string_of_bytestring (snd p)))

let write_lean_res opts f p =
  let f = get_out_file opts f "lean" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_fsharp_res opts f p =
  let f = get_out_file opts f "fs" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_koka_res opts f p =
  let f = get_out_file opts f "kk" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_ast_res opts f p =
  let f = get_out_file opts f "ast" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let printCProg prog names (dest : string) (imports : import list) =
  let imports' = List.map (fun i -> match i with
    | FromRelativePath s -> "#include \"" ^ s ^ "\""
    | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
    | FromAbsolutePath _ ->
        failwith "Import with absolute path should have been filled") imports in
  Peregrine.PrintClight.print_dest_names_imports prog (Anf_term.M.elements names) dest imports'

let write_c_res opts f p =
  match p with
  | (((nenv, header), prg), libs) ->
    let runtime_imports = List.map (fun x -> FromLibrary (caml_string_of_bytestring x, None)) libs in
    let imports = runtime_imports in
    let cstr = get_out_file opts f "c" in
    let hstr = get_header_file opts f in
    (* The header is written next to the .c, so include it by basename *)
    printCProg prg nenv cstr (imports @ [FromRelativePath (Filename.basename hstr)]);
    printCProg header nenv hstr (runtime_imports)

let write_program opts f p =
  match p with
  | Pipeline.RustProgram p -> write_rust_res opts f p
  | Pipeline.ElmProgram p -> write_elm_res opts f p
  | Pipeline.OCamlProgram p -> write_ocaml_res opts f p
  | Pipeline.CakeMLProgram p -> write_cakeml_res opts f p
  | Pipeline.CProgram p -> write_c_res opts f p
  | Pipeline.WasmProgram p -> write_wasm_res opts f p
  | Pipeline.LLVMProgram p -> write_llvm_res opts f p
  | Pipeline.LeanProgram p -> write_lean_res opts f p
  | Pipeline.FSharpProgram p -> write_fsharp_res opts f p
  | Pipeline.KokaProgram p -> write_koka_res opts f p
  | Pipeline.EvalProgram p -> cprint_endline p
  | Pipeline.ASTProgram p -> write_ast_res opts f p



let mk_certirocq_config copts = {
  ConfigUtils.direct'    = Some (not copts.cps);
  ConfigUtils.c_args'    = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.c_args;
  ConfigUtils.o_level'   = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.o_level;
  ConfigUtils.anf_conf'  = None;
  ConfigUtils.prefix'    = None;
  ConfigUtils.body_name' = Option.map bytestring_of_caml_string copts.body_name;
}

(* The erasure phases of [base] (a configuration file's, or none), with the
   passes given on the command line overriding them. Beta reduction and
   constant lifting, which the default pass set has, are on where neither
   sets them, unless -O0. implement box and implement lazy are the backend's
   choice (ConfigUtils.enforce_phases). *)
let mk_erasure_config ?base (p : passes) =
  let ov cli file = match cli with Some _ -> cli | None -> file in
  let default = if p.optimize then Some true else None in
  let b = match base with
    | Some b -> b
    | None -> { ConfigUtils.implement_box' = None; implement_lazy' = None;
                betared' = None; unboxing' = None; dearg_ctors' = None;
                dearg_consts' = None; specialize_instances' = None;
                cse' = None; lift_constants' = None; untyped_dearg' = None } in
  { b with
    ConfigUtils.betared'        = ov p.beta_reduce (ov b.ConfigUtils.betared' default);
    ConfigUtils.unboxing'       = ov p.unbox b.ConfigUtils.unboxing';
    ConfigUtils.dearg_consts'   = ov p.dearg_constants b.ConfigUtils.dearg_consts';
    ConfigUtils.specialize_instances' = ov p.specialize_instances b.ConfigUtils.specialize_instances';
    ConfigUtils.cse'            = ov p.share_common_subterms b.ConfigUtils.cse';
    ConfigUtils.lift_constants' = ov p.lift_constants (ov b.ConfigUtils.lift_constants' default);
    ConfigUtils.untyped_dearg'  = ov p.untyped_dearg b.ConfigUtils.untyped_dearg';
  }

(* Does the command line, or the default pass set, set an erasure phase (one
   of those of a configuration file)? *)
let sets_erasure_phase (p : passes) =
  p.optimize || List.exists Option.is_some
    [p.beta_reduce; p.unbox; p.dearg_constants; p.specialize_instances;
     p.share_common_subterms; p.lift_constants; p.untyped_dearg]

let mk_config ?(const_remaps=[]) ?(ind_remaps=[]) b passes = {
  ConfigUtils.backend_opts' = b;
  ConfigUtils.erasure_opts' = Some (mk_erasure_config passes);
  ConfigUtils.inlinings_opts' = [];
  ConfigUtils.const_remappings_opts' = const_remaps;
  ConfigUtils.ind_remappings_opts' = ind_remaps;
  ConfigUtils.cstr_reorders_opts' = [];
  ConfigUtils.custom_attributes_opts' = []
}

let mk_ast_config t copts : ConfigUtils.ast_config' =
    match t with
    | Box -> ConfigUtils.LambdaBox'
    | BoxTyped -> ConfigUtils.LambdaBoxTyped'
    | ANF -> ConfigUtils.LambdaANF' (Some (mk_certirocq_config copts))
    | ANFC -> ConfigUtils.LambdaANFC' (Some (mk_certirocq_config copts))

let info opts s = if opts.verbose <> Quiet then print_endline s

let read_attrs opts attrs =
  List.map (fun s -> s |> read_file |> bytestring_of_caml_string) (opts.attrs @ attrs)

(* Validate function *)
let validate opts fo f_input f_config =
  let f_prog, attrs, _ = Frontend.load opts fo ~typed:false f_input in
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  (* backend part of config isn't check so we just use any *)
  let config =
    match f_config with
    | Some f -> Datatypes.Coq_inl (f |> read_file |> bytestring_of_caml_string)
    | None -> Datatypes.Coq_inr (ConfigUtils.empty_config' (ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config')) in
  let attrs = read_attrs opts attrs in
  info opts "Validating AST:";
  let res = Pipeline.peregrine_validate config attrs prog in
  match res with
  | ResultMonad.Ok _ ->
    info opts "AST is valid"
  | ResultMonad.Err e ->
    print_endline "Error validating AST:";
    cprint_endline e;
    exit 1


(* Compile functions *)
(* The lambda-box simplification passes (ELboxOpts.v) *)
let mk_lbox_opts (p : passes) =
  { Peregrine.ELboxOpts.lbox_fix_eta = p.unwrap_fixpoints;
    lbox_case_fun = p.hoist_case_lambdas;
    lbox_case_id = p.drop_identity_matches;
    lbox_let_fun = p.inline_atomic_lets;
    lbox_iota = p.iota_reduce }

(* Automatic inlining (AutoInlining.v) *)
let mk_inline_opts (p : passes) =
  { Peregrine.AutoInlining.inline_standard = p.inline_standard_constants;
    inline_small = p.inline_small_constants;
    inline_size_limit = Peregrine.Caml_nat.nat_of_caml_int (max 0 p.inline_size_limit);
    inline_excluded = List.map bytestring_of_caml_string p.no_inline }

let compile_aux opts fo ~typed f_input config =
  let f_prog, attrs, stem = Frontend.load opts fo ~typed f_input in
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  let f_name = stem |> Filename.basename |> bytestring_of_caml_string in
  let attrs = read_attrs opts attrs in
  info opts "Compiling:";
  (* [notes]: skipped optimizations (PipelineParse.dearging_warnings), which
     do not affect correctness; [warnings]: programs outside verified
     extraction's correctness theorem, rejected by --strict-verified. *)
  let res = PipelineParse.peregrine_pipeline_warn config attrs opts.passes.inline_recursors (mk_inline_opts opts.passes) (mk_lbox_opts opts.passes) prog f_name in
  let print_warnings = List.iter (fun w -> prerr_endline ("Warning: " ^ caml_string_of_bytestring w)) in
  match res with
  | ResultMonad.Ok (notes, (_ :: _ as warnings, _)) when opts.strict_verified ->
    print_warnings notes;
    print_endline "Could not compile:";
    List.iter cprint_endline warnings;
    exit 1
  | ResultMonad.Ok (notes, (warnings, p)) ->
    print_warnings notes;
    print_warnings warnings;
    info opts "Compiled successfully:";
    (* The only output that can have the name of a source: lean on a .lean *)
    (match p with
     | Pipeline.LeanProgram _ when get_out_file opts stem "lean" = f_input ->
       prerr_endline ("peregrine: the output would overwrite " ^ f_input ^ ", give another output file with -o");
       exit 1
     | _ -> write_program opts stem p)
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    cprint_endline e;
    exit 1

let compile opts fo f_prog f_config =
  let config = f_config |> read_file |> bytestring_of_caml_string in
  (* A frontend gives typed lambda box to the backends that need it *)
  let typed = match Pipeline.parse_config config with
    | ResultMonad.Ok { Config.backend_opts = (Config.Rust _ | Config.Elm _ | Config.AST Config.LambdaBoxTyped); _ } -> true
    | _ -> false in
  (* The passes given on the command line override the file's erasure
     phases, which override the default pass set. If the file does not
     parse, the pipeline reports it. *)
  let config =
    if not (sets_erasure_phase opts.passes) then Datatypes.Coq_inl config
    else match Peregrine.Deserialize.config_of_string config with
      | Datatypes.Coq_inr c ->
        Datatypes.Coq_inr { c with ConfigUtils.erasure_opts' =
          Some (mk_erasure_config ?base:c.ConfigUtils.erasure_opts' opts.passes) }
      | Datatypes.Coq_inl _ -> Datatypes.Coq_inl config in
  compile_aux opts fo ~typed f_prog config

(* Write the lambda box program of a source file, and the attribute files of
   its frontend next to it *)
let erase opts fo f_input =
  let f_prog, attrs, stem = Frontend.load opts fo ~typed:false f_input in
  if f_prog = f_input then
    Frontend.fail Frontend.unsupported "%s is a lambda box program already" f_input;
  let out = get_out_file opts stem "ast" in
  Frontend.copy f_prog out;
  List.iter (fun a -> Frontend.copy a (out ^ Filename.extension a)) attrs

(* A backend configuration with its remappings. [typed] asks the frontend for
   typed lambda box. *)
type target = {
  backend : ConfigUtils.backend_config';
  const_remaps : Config.constant_remappings;
  ind_remaps : Config.inductive_remappings;
  typed : bool;
}

let target ?(typed=false) ?(const_remaps=[]) ?(ind_remaps=[]) backend =
  { backend; const_remaps; ind_remaps; typed }

let compile_backend t opts fo f_prog =
  let config = mk_config ~const_remaps:t.const_remaps ~ind_remaps:t.ind_remaps t.backend opts.passes in
  compile_aux opts fo ~typed:t.typed f_prog (Datatypes.Coq_inr config)

(* The representations of nat/positive/N/Z in Rust, chosen by `rust
   --rust-numbers`. Each also has its own, deprecated, verb. *)
type rust_numbers = {
  rust_numbers : string;
  rust_verb_name : string;
  rust_verb_doc : string;
  rust_verb_config : ConfigUtils.rust_config';
  rust_verb_const_remaps : Config.constant_remappings;
  rust_verb_ind_remaps : Config.inductive_remappings;
}

let rust_numbers = [
  { rust_numbers = "peano";
    rust_verb_name = "rust";
    rust_verb_doc = "the inductive types as extracted (unary nat, binary positive/N/Z), no remapping";
    rust_verb_config = ConfigUtils.empty_rust_config';
    rust_verb_const_remaps = [];
    rust_verb_ind_remaps = [] };
  { rust_numbers = "gmp";
    rust_verb_name = "rust-gmp";
    rust_verb_doc = "GMP integers (rug::Integer, needs the rug crate)";
    rust_verb_config = RustGMPRemaps.gmp_rust_config';
    rust_verb_const_remaps = RustGMPRemaps.gmp_const_remaps;
    rust_verb_ind_remaps = RustGMPRemaps.gmp_ind_remaps };
  { rust_numbers = "i64";
    rust_verb_name = "rust-i64";
    rust_verb_doc = "i64, overflow is not checked";
    rust_verb_config = RustNativeRemaps.native_rust_config';
    rust_verb_const_remaps = RustNativeRemaps.native_const_remaps;
    rust_verb_ind_remaps = RustNativeRemaps.native_ind_remaps };
  { rust_numbers = "mixed";
    rust_verb_name = "rust-mixed";
    rust_verb_doc = "GMP integers, with add/mul/sub/div/mod/pow/eqb/leb/ltb on nat computed in i64";
    rust_verb_config = RustMixedRemaps.mixed_rust_config';
    rust_verb_const_remaps = RustMixedRemaps.mixed_const_remaps;
    rust_verb_ind_remaps = RustMixedRemaps.mixed_ind_remaps };
  { rust_numbers = "mixed-narrow";
    rust_verb_name = "rust-mixed-narrow";
    rust_verb_doc = "GMP integers, with div/mod/pow on nat computed in i64";
    rust_verb_config = RustMixedRemaps.mixed_rust_config';
    rust_verb_const_remaps = RustMixedRemaps.mixed_const_remaps2;
    rust_verb_ind_remaps = RustMixedRemaps.mixed_ind_remaps };
  { rust_numbers = "hybrid";
    rust_verb_name = "rust-hybrid";
    rust_verb_doc = "i64 when the value fits and GMP integers otherwise, overflow checked (needs the rug crate)";
    rust_verb_config = RustHybridRemaps.hybrid_rust_config';
    rust_verb_const_remaps = RustHybridRemaps.hybrid_const_remaps;
    rust_verb_ind_remaps = RustHybridRemaps.hybrid_ind_remaps };
]

let rust_target v =
  target ~typed:true ~const_remaps:v.rust_verb_const_remaps ~ind_remaps:v.rust_verb_ind_remaps
    (ConfigUtils.Rust' v.rust_verb_config)

let eval_target copts fuel =
  target (ConfigUtils.Eval' {
      ConfigUtils.copts'    = Some (mk_certirocq_config copts);
      ConfigUtils.fuel'     = Peregrine.Caml_nat.nat_of_caml_int fuel;
    })

let ast_target copts t =
  target ~typed:(t = BoxTyped) (ConfigUtils.AST' (mk_ast_config t copts))
