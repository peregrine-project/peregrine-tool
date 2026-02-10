From Peregrine Require Import Serialize.
From Peregrine Require Import PAst.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import Transforms.
From Peregrine Require Import Erasure.
From Peregrine Require Import CheckWf.
From Peregrine Require RustBackend.
From Peregrine Require ElmBackend.
From Peregrine Require OCamlBackend.
From Peregrine Require CBackend.
From Peregrine Require WasmBackend.
From Peregrine Require TypedTransforms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.

Import MRMonadNotation.
#[local]
Existing Instance Monad_result.

Local Open Scope bs_scope.



Definition parse_ast (s : string) : result PAst string :=
  match PAst_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing input program\n" ++ string_of_error true true e)
  end.

Definition parse_config (s : string) : result config string :=
  match config_of_string s with
  | inr p => Ok (mk_config p)
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attribute (s : string) : result attributes_config string :=
  match attributes_config_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attributes (attrs : list string) : result (list attributes_config) string :=
  monad_map parse_attribute attrs.

Definition get_config (c : string + config') (attrs : list string) : result config string :=
  c <- match c with
      | inl s => parse_config s
      | inr c' => Ok (mk_config c')
      end;;
  attrs <- parse_attributes attrs;;
  if 0 <? length attrs then Ok (merge_attributes_config c attrs) else Ok c.

Definition check_wf (p : PAst) : result unit string :=
  map_error (fun e => "Program not wellformed\n" ++ e)
  match p with
  | Untyped env (Some t) =>
      @check_wf_program EWellformed.all_env_flags (env, t)
  | Untyped env None =>
      @check_wf_glob EWellformed.all_env_flags env
  | Typed env (Some t) =>
      _ <- @CheckWfExAst.check_wf_typed_program EWellformed.all_env_flags env;;
      @wellformed EWellformed.all_env_flags (ExAst.trans_env env) 0 t
  | Typed env None =>
      @CheckWfExAst.check_wf_typed_program EWellformed.all_env_flags env
  end.

(* TODO: move *)
Definition assert {E : Type} (b : bool) (e : E) : result unit E :=
  if b then Ok tt else Err e.

Definition validate_ast_type (c : config) (p : PAst) : result unit string :=
  match c.(backend_opts) with
  | Rust _ => assert (is_typed_ast p) "Rust extraction requires typed lambda box input"
  | Elm _ => assert (is_typed_ast p) "Elm extraction requires typed lambda box input"
  | C _ | Wasm _ | OCaml _ | CakeML _ => Ok tt
  end.

Definition needs_typed (c : config) : bool :=
  match c.(backend_opts) with
  | Rust _ | Elm _ => true
  | C _ | Wasm _ | OCaml _ | CakeML _ => false
  end.

Definition apply_transforms (c : config) (p : PAst) (typed : bool) : result PAst string :=
  let econf := mk_opts c typed in
  let cstr_reorder := mk_cstr_reorders c in
  let impl_box := c.(erasure_opts).(implement_box) in
  let impl_lazy := c.(erasure_opts).(implement_lazy) in
  match p, typed with
  | Untyped env (Some t), _ =>
      let (env', t') := run_untyped_transforms econf cstr_reorder impl_box impl_lazy (env, t) in
      Ok (Untyped env' (Some t'))
  | Untyped env None, _ =>
      let (env', _) := run_untyped_transforms econf cstr_reorder impl_box impl_lazy (env, EAst.tBox) in
      Ok (Untyped env' None)
  | Typed env (Some t), true =>
      let '(_, (env', t')) := run_typed_transforms econf cstr_reorder (env, t) in
      Ok (Typed env' (Some t'))
  | Typed env (Some t), false =>
      let (env', t') := run_typed_to_untyped_transforms econf cstr_reorder impl_box impl_lazy (env, t) in
      (Ok (Untyped env' (Some t')))
  | Typed env None, true =>
      let '(_, (env', _)) := run_typed_transforms econf cstr_reorder (env, EAst.tBox) in
      Ok (Typed env' None)
  | Typed env None, false =>
      let (env', _) := run_typed_to_untyped_transforms econf cstr_reorder impl_box impl_lazy (env, EAst.tBox) in
      (Ok (Untyped env' None))
  end.



Inductive extracted_program :=
| RustProgram : list string -> extracted_program
| ElmProgram : string -> extracted_program
| CProgram : (CertiCoq.Codegen.toplevel.Cprogram * list string) -> extracted_program
| WasmProgram : string -> extracted_program
| OCamlProgram : (list string * string) -> extracted_program
| CakeMLProgram : (list string * string) -> extracted_program.

Definition extraction_result : Type := result extracted_program string.

Definition run_backend (c : config) (f : string) (p : PAst) : extraction_result :=
  let remaps := c.(remappings_opts) in
  let custom_attr := c.(custom_attributes_opts) in
  match c.(backend_opts) with
  | Rust opts =>
    p' <- PAst_to_ExAst p;;
    res <- RustBackend.extract_rust
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (RustProgram res)

  | Elm opts =>
    p' <- PAst_to_ExAst p;;
    res <- ElmBackend.extract_elm
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (ElmProgram res)

  | OCaml opts =>
    p' <- PAst_to_EAst p;;
    res <- OCamlBackend.extract_ocaml
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (OCamlProgram res)

  | CakeML opts =>
    p' <- PAst_to_EAst p;;
    res <- CakeMLBackend.extract_cakeml
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (CakeMLProgram res)

  | C opts =>
    p' <- PAst_to_EAst p;;
    res <- CBackend.extract_c
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (CProgram res)

  | Wasm opts =>
    p' <- PAst_to_EAst p;;
    res <- WasmBackend.extract_wasm
      remaps
      custom_attr
      opts
      f
      p';;
    Ok (WasmProgram res)
  end.



Definition peregrine_pipeline (c : string + config') (attrs : list string) (p : string) (f : string) : extraction_result :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c attrs;; (* Parse or construct config *)
  check_wf p;; (* Check that AST is wellformed *)
  validate_ast_type c p;; (* Check that the provided AST is compatible with the chosen backend *)
  p <- apply_transforms c p (needs_typed c);; (* Apply program transformation *)
  run_backend c f p. (* Run extraction backend *)
