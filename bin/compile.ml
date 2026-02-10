open Common
open Peregrine.Caml_bytestring

module Datatypes = Peregrine.Datatypes
module CeresExtra = Peregrine.CeresExtra
module Config = Peregrine.Config1
module ConfigUtils = Peregrine.ConfigUtils
module Pipeline = Peregrine.Pipeline1
module CompM = Peregrine.CompM
module ResultMonad = Peregrine.ResultMonad
module Cps = Peregrine.Cps



(* String conversion *)
let string_of_cstring = Peregrine.Camlcoq.camlstring_of_coqstring
let cstring_of_string = Peregrine.Camlcoq.coqstring_of_camlstring

let cprint_endline s =
  print_endline (caml_string_of_bytestring s)



(* Extraction output helper functions *)
let get_out_file opts f ext =
  match opts.output_file with
  | Some f -> f
  | None -> (Filename.remove_extension f)^"."^ext

let get_header_file opts f =
  match opts.output_file with
  | Some f -> (Filename.remove_extension f)^".h"
  | None -> (Filename.remove_extension f)^".h"

let write_res f p =
  let f = open_out f in
  p f;
  flush f;
  close_out f

let write_wasm_res opts f p =
  let f = get_out_file opts f "wasm" in
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

let printCProg prog names (dest : string) (imports : import list) =
  let imports' = List.map (fun i -> match i with
    | FromRelativePath s -> "#include \"" ^ s ^ "\""
    | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
    | FromAbsolutePath _ ->
        failwith "Import with absolute path should have been filled") imports in
  Peregrine.PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

let write_c_res opts f p =
  match p with
  | (((nenv, header), prg), libs) ->
    let runtime_imports = List.map (fun x -> FromLibrary (caml_string_of_bytestring x, None)) libs in
    let imports = runtime_imports in
    let cstr = get_out_file opts f "c" in
    let hstr = get_header_file opts f in
    printCProg prg nenv cstr (imports @ [FromRelativePath hstr]);
    printCProg header nenv hstr (runtime_imports)

let write_program opts f p =
  match p with
  | Pipeline.RustProgram p -> write_rust_res opts f p
  | Pipeline.ElmProgram p -> write_elm_res opts f p
  | Pipeline.OCamlProgram p -> write_ocaml_res opts f p
  | Pipeline.CProgram p -> write_c_res opts f p
  | Pipeline.WasmProgram p -> write_wasm_res opts f p



let read_file f =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  s



(* Compile functions *)
let compile_aux opts f prog config =
  let f_name = f |> Filename.basename |> Filename.chop_extension |> bytestring_of_caml_string in
  let attrs = List.map bytestring_of_caml_string opts.attrs in
  print_endline "Compiling:";
  let res = Pipeline.peregrine_pipeline config attrs prog f_name in
  match res with
  | ResultMonad.Ok p ->
    print_endline "Compiled successfully:";
    write_program opts f p
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    cprint_endline e;
    exit 1

let compile opts f_prog f_config =
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  let config = f_config |> read_file |> bytestring_of_caml_string in
  compile_aux opts f_prog prog (Datatypes.Coq_inl config)

let compile_backend backend_opts opts f_prog =
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  let config = backend_opts |> ConfigUtils.empty_config' in
  compile_aux opts f_prog prog (Datatypes.Coq_inr config)

let compile_rust opts f_prog =
  let b_opts = ConfigUtils.Rust' ConfigUtils.empty_rust_config' in
  compile_backend b_opts opts f_prog

let compile_elm opts f_prog =
  let b_opts = ConfigUtils.Elm' ConfigUtils.empty_elm_config' in
  compile_backend b_opts opts f_prog

let compile_ocaml opts f_prog =
  let b_opts = ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config' in
  compile_backend b_opts opts f_prog



let mk_certicoq_config copts = {
  ConfigUtils.direct'    = Some (not copts.cps);
  ConfigUtils.c_args'    = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.c_args;
  ConfigUtils.o_level'   = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.o_level;
  ConfigUtils.prefix'    = Option.map bytestring_of_caml_string copts.prefix;
  ConfigUtils.body_name' = Option.map bytestring_of_caml_string copts.body_name;
}


let compile_c opts copts f_prog =
  let b_opts = ConfigUtils.C' (mk_certicoq_config copts) in
  compile_backend b_opts opts f_prog

let compile_wasm opts copts f_prog =
  let b_opts = ConfigUtils.Wasm' (mk_certicoq_config copts) in
  compile_backend b_opts opts f_prog
