From Peregrine Require Import Serialize.
From Peregrine Require Import PAst.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import Transforms.
From Peregrine Require Import Erasure.
From Peregrine Require Import CheckWf.
From Peregrine Require LambdaBoxToRust.
From Peregrine Require LambdaBoxToElm.
From Peregrine Require LambdaBoxToOCaml.
From Peregrine Require LambdaBoxToC.
From Peregrine Require LambdaBoxToWasm.
From Peregrine Require TypedTransforms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.

Import MRMonadNotation.

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

Definition get_config (c : string + config') : result config string :=
  match c with
  | inl s => parse_config s
  | inr c' => Ok (mk_config c')
  end.

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
  | C _ | Wasm _ | OCaml _ => Ok tt
  end.

Definition needs_typed (c : config) : bool :=
  match c.(backend_opts) with
  | Rust _ | Elm _ => true
  | C _ | Wasm _ | OCaml _ => false
  end.

Definition apply_transforms (c : config) (p : PAst) (typed : bool) : result PAst string :=
  let econf := mk_opts c typed in
  let cstr_reorder := mk_cstr_reorders c in
  let impl_box := c.(erasure_opts).(phases).(implement_box) in
  let impl_lazy := c.(erasure_opts).(phases).(implement_lazy) in
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
| CProgram : CertiCoq.Codegen.toplevel.Cprogram -> extracted_program
| WasmProgram : string -> extracted_program
| OCamlProgram : (list string * string) -> extracted_program.

Definition extraction_result : Type := result extracted_program string.

#[local]
Existing Instance Monad_result.

Definition run_backend (c : config) (f : string) (p : PAst) : extraction_result :=
  match c.(backend_opts) with
  | Rust opts =>
    p' <- PAst_to_ExAst p;;
    res <- LambdaBoxToRust.box_to_rust
      LambdaBoxToRust.default_remaps
      (LambdaBoxToRust.mk_preamble None None)
      LambdaBoxToRust.default_attrs
      TypedTransforms.default_params
      p';;
    Ok (RustProgram res)

  | Elm opts =>
    p' <- PAst_to_ExAst p;;
    res <- LambdaBoxToElm.box_to_elm
      f
      None
      LambdaBoxToElm.default_remaps
      TypedTransforms.default_params
      p';;
    Ok (ElmProgram res)

  | OCaml opts =>
    p' <- PAst_to_EAst p;;
    let res := LambdaBoxToOCaml.box_to_ocaml p' in
    Ok (OCamlProgram res)

  | C opts =>
    p' <- PAst_to_EAst p;;
    let opts := CertiCoqPipeline.make_opts false false in
    match LambdaBoxToC.run_translation opts p' with
    | (compM.Ret prg, _) => Ok (CProgram prg)
    | (compM.Err e, _) => Err e
    end

  | Wasm opts =>
    p' <- PAst_to_EAst p;;
    let opts := CertiCoqPipeline.make_opts false false in
    match LambdaBoxToWasm.run_translation opts p' with
    | (compM.Ret prg, _) => Ok (WasmProgram prg)
    | (compM.Err e, _) => Err e
    end
  end.

Definition peregrine_pipeline (c : string + config') (p : string) (f : string) : extraction_result :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c;; (* Parse or construct config *)
  check_wf p;; (* Check that AST is wellformed *)
  validate_ast_type c p;; (* Check that the provided AST is compatible with the chosen backend *)
  p <- apply_transforms c p (needs_typed c);; (* Apply program transformation *)
  run_backend c f p. (* Run extraction backend *)
