From Peregrine Require Import Deserialize.
From Peregrine Require Import PAst.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import Transforms.
From Peregrine Require Import EExtraFlags.
From Peregrine Require Import Erasure.
From Peregrine Require Import CheckWf.
From Peregrine Require Import RecursorInlining.
From Peregrine Require Import ELboxOpts.
From Peregrine Require RustBackend.
From Peregrine Require ElmBackend.
From Peregrine Require OCamlBackend.
From Peregrine Require CBackend.
From Peregrine Require WasmBackend.
From Peregrine Require LeanBackend.
From Peregrine Require LLVMBackend.
From Peregrine Require FSharpBackend.
From Peregrine Require KokaBackend.
From Peregrine Require KokaTypedBackend.
From Peregrine Require EvalBackend.
From Peregrine Require ASTBackend.
From Peregrine Require NameSanitize.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Utils.

Import MonadNotation.

Local Open Scope bs_scope.



Definition parse_ast (s : string) : result' PAst :=
  match PAst_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing input program\n" ++ string_of_error true true e)
  end.

Definition parse_config (s : string) : result' config :=
  match config_of_string s with
  | inr p => Ok (mk_config p)
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attribute (s : string) : result' attributes_config :=
  match attributes_config_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attributes (attrs : list string) : result' (list attributes_config) :=
  monad_map parse_attribute attrs.

Definition get_config (c : string + config') (attrs : list string) : result' config :=
  c <- match c with
      | inl s => parse_config s
      | inr c' => Ok (mk_config c')
      end;;
  attrs <- parse_attributes attrs;;
  if 0 <? length attrs then Ok (merge_attributes_config c attrs) else Ok c.

(* Peregrine does not support cofixpoints: [nocofix_env_flags] rejects them, and
   the middle-end passes are proved correct at these flags. *)
Definition check_wf (p : PAst) : result' unit :=
  map_error (fun e => "Program not wellformed\n" ++ e)
  match p with
  | Untyped env (Some t) =>
      @check_wf_program nocofix_env_flags (env, t)
  | Untyped env None =>
      @check_wf_glob nocofix_env_flags env
  | Typed env (Some t) =>
      _ <- @CheckWfExAst.check_wf_typed_program nocofix_env_flags env;;
      @wellformed nocofix_env_flags (ExAst.trans_env env) 0 t
  | Typed env None =>
      @CheckWfExAst.check_wf_typed_program nocofix_env_flags env
  end.

Definition needs_typed (c : config) : bool :=
  match c.(backend_opts) with
  | Rust _ | Elm _ | KokaTyped _ => true
  | C _ | Wasm _ | LLVM _ | OCaml _ | CakeML _ | Lean _ | FSharp _ | Koka _ | Eval _ => false
  | AST c =>
    match c.(ast_type) with
    | LambdaBoxTyped => true
    | _ => false
    end
  end.

(* A remapped constant is an axiom to the typed transforms: its body is not used,
   and an analysis of that body must not decide the parameters of the constant.
   Dearging would otherwise remove a parameter that the body ignores, and the
   remapping, which takes that parameter, would no longer match its calls.  The
   mask of a constant without a body removes the logical parameters only. *)
Definition drop_remapped_bodies (c : config) (env : ExAst.global_env) : ExAst.global_env :=
  map (fun '(kn, deps, d) =>
    match d with
    | ExAst.ConstantDecl cst =>
      if existsb (fun '(kn', _) => Kernames.eq_kername kn kn') c.(const_remappings_opts)
      then (kn, deps, ExAst.ConstantDecl {| ExAst.cst_type := cst.(ExAst.cst_type); ExAst.cst_body := None |})
      else (kn, deps, d)
    | _ => (kn, deps, d)
    end) env.

(** The lambda-box simplifications of ELboxOpts.v selected by [lbox] are part
    of the transformation chain of the typed pipeline
    ([Transforms.typed_lbox_transform_pipeline]), as they are for the untyped
    one. *)

(** The transformation pipelines check their precondition on their actual
    input (after sanitization, inference and dropping remapped bodies) and
    fail with an error if it does not hold. *)
Definition pipeline_pre_error {A} (r : result' A) : result' A :=
  map_error (fun e => "Program does not satisfy the precondition of the transformation pipeline: " ++ e) r.

Definition apply_transforms (c : config) (lbox : lbox_opts) (p : PAst) (typed : bool) : result' PAst :=
  let drop := drop_remapped_bodies c in
  (* Untyped input: MetaRocq's dearging analysis as is. A typed environment: the
     masks of remapped constants from their types ([remap_masks]), with every
     argument kept after the type inference of untyped input. *)
  let econf := mk_opts c typed (fun _ => None) in
  let tconf env := mk_opts c typed (remap_masks c false env) in
  let iconf env := mk_opts c typed (remap_masks c true env) in
  let cstr_reorder := mk_cstr_reorders c in
  let impl_box := c.(erasure_opts).(implement_box) in
  let impl_lazy := c.(erasure_opts).(implement_lazy) in
  let spec_inst := c.(erasure_opts).(specialize_instances) in
  let cse := c.(erasure_opts).(cse) in
  let lift_consts := c.(erasure_opts).(lift_constants) in
  match p, typed with
  | Untyped env (Some t), true =>
      (* Typed backend on untyped (lambda-box) input: bridge to typed via the
         HM inference [infer_for_backend] on the *raw* env (before the
         untyped pipeline turns constructors into blocks, which the typed
         backends do not consume), then run the typed pipeline, which
         preserves applied constructors.  Inference failure is a pipeline
         error.  [EHindleyMilner.infer_section] gives [trans_env env0 = env];
         nothing is proved about the inferred types. *)
      env0 <- infer_for_backend env;;
      r <- pipeline_pre_error (run_typed_transforms (iconf env0) cstr_reorder lbox (drop env0, t));;
      let '(_, (env', t')) := r in
      Ok (Typed env' (Some t'))
  | Untyped env None, true =>
      env0 <- infer_for_backend env;;
      r <- pipeline_pre_error (run_typed_transforms (iconf env0) cstr_reorder lbox (drop env0, EAst.tBox));;
      let '(_, (env', _)) := r in
      Ok (Typed env' None)
  | Untyped env (Some t), false =>
      r <- pipeline_pre_error (run_untyped_transforms econf cstr_reorder spec_inst cse lbox lift_consts impl_box impl_lazy (env, t));;
      let (env', t') := r in
      Ok (Untyped env' (Some t'))
  | Untyped env None, false =>
      r <- pipeline_pre_error (run_untyped_transforms econf cstr_reorder spec_inst cse lbox lift_consts impl_box impl_lazy (env, EAst.tBox));;
      let (env', _) := r in
      Ok (Untyped env' None)
  | Typed env (Some t), true =>
      r <- pipeline_pre_error (run_typed_transforms (tconf env) cstr_reorder lbox (drop env, t));;
      let '(_, (env', t')) := r in
      Ok (Typed env' (Some t'))
  | Typed env (Some t), false =>
      r <- pipeline_pre_error (run_typed_to_untyped_transforms (tconf env) cstr_reorder spec_inst cse lbox lift_consts impl_box impl_lazy (drop env, t));;
      let (env', t') := r in
      (Ok (Untyped env' (Some t')))
  | Typed env None, true =>
      r <- pipeline_pre_error (run_typed_transforms (tconf env) cstr_reorder lbox (drop env, EAst.tBox));;
      let '(_, (env', _)) := r in
      Ok (Typed env' None)
  | Typed env None, false =>
      r <- pipeline_pre_error (run_typed_to_untyped_transforms (tconf env) cstr_reorder spec_inst cse lbox lift_consts impl_box impl_lazy (drop env, EAst.tBox));;
      let (env', _) := r in
      (Ok (Untyped env' None))
  end.



Inductive extracted_program :=
| RustProgram : list string -> extracted_program
| ElmProgram : string -> extracted_program
| CProgram : (CertiRocq.Codegen.toplevel.Cprogram * list string) -> extracted_program
| WasmProgram : string -> extracted_program
| LLVMProgram : string -> extracted_program
| OCamlProgram : (list string * string) -> extracted_program
| CakeMLProgram : (list string * string) -> extracted_program
| LeanProgram : string -> extracted_program
| FSharpProgram : string -> extracted_program
| KokaProgram : string -> extracted_program
| EvalProgram : string -> extracted_program
| ASTProgram : string -> extracted_program.

Definition extraction_result : Type := result' extracted_program.

Definition run_backend (c : config) (f : string) (p : PAst) : extraction_result :=
  let const_remaps := c.(const_remappings_opts) in
  let ind_remaps := c.(ind_remappings_opts) in
  let custom_attr := c.(custom_attributes_opts) in
  match c.(backend_opts) with
  | Rust opts =>
    p' <- PAst_to_ExAst p;;
    res <- RustBackend.extract_rust
      const_remaps
      ind_remaps
      custom_attr
      opts
      f
      p';;
    Ok (RustProgram res)

  | Elm opts =>
    p' <- PAst_to_ExAst p;;
    res <- ElmBackend.extract_elm
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (ElmProgram res)

  | OCaml opts =>
    p' <- PAst_to_EAst p;;
    res <- OCamlBackend.extract_ocaml
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (OCamlProgram res)

  | CakeML opts =>
    p' <- PAst_to_EAst p;;
    res <- CakeMLBackend.extract_cakeml
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (CakeMLProgram res)

  | FSharp opts =>
    p' <- PAst_to_EAst p;;
    res <- FSharpBackend.extract_fsharp
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (FSharpProgram res)

  | Koka opts =>
    p' <- PAst_to_EAst p;;
    res <- KokaBackend.extract_koka
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (KokaProgram res)

  | KokaTyped opts =>
    p' <- PAst_to_ExAst p;;
    res <- KokaTypedBackend.extract_koka_typed
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (KokaProgram res)

  | C opts =>
    p' <- PAst_to_EAst p;;
    res <- CBackend.extract_c
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (CProgram res)

  | Wasm opts =>
    p' <- PAst_to_EAst p;;
    res <- WasmBackend.extract_wasm
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (WasmProgram res)

  | LLVM opts =>
    p' <- PAst_to_EAst p;;
    res <- LLVMBackend.extract_llvm
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (LLVMProgram res)

  | Lean opts =>
    p' <- PAst_to_EAst p;;
    (* The file name is spliced into every emitted identifier. *)
    f <- Unicode.of_string f;;
    res <- LeanBackend.extract_lean
      const_remaps
      custom_attr
      opts
      (NameSanitize.lean_sanitizer f)
      p';;
    Ok (LeanProgram res)

  | Eval opts =>
    p' <- PAst_to_EAst p;;
    res <- EvalBackend.eval
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (EvalProgram res)

  | AST opts =>
    res <- ASTBackend.extract_ast
      const_remaps
      custom_attr
      opts
      f
      p;;
    Ok (ASTProgram res)
  end.



(* The first term that CertiRocq and the verified Malfunction and CakeML
   compilers have no translation for.  They turn such a term into a placeholder,
   so the program would compile and then crash or compute a wrong result.
   [check_wf] already rejects cofixpoints; [implement_lazy] removes lazy and
   force. *)
Fixpoint unlowered_term (t : EAst.term) : option string :=
  let first := fix first (l : list (option string)) :=
    match l with
    | [] => None
    | Some s :: _ => Some s
    | None :: l => first l
    end in
  match t with
  | EAst.tLazy _ | EAst.tForce _ => Some "lazy and force"
  | EAst.tLambda _ b | EAst.tProj _ b => unlowered_term b
  | EAst.tLetIn _ b u | EAst.tApp b u =>
    first [unlowered_term b; unlowered_term u]
  | EAst.tConstruct _ _ args => first (List.map unlowered_term args)
  | EAst.tCase _ d brs =>
    first (unlowered_term d :: List.map (fun br => unlowered_term (snd br)) brs)
  | EAst.tFix mfix _ => first (List.map (fun d => unlowered_term d.(EAst.dbody)) mfix)
  | _ => None
  end.

Definition check_lowered_program (backend : string) (p : EAst.program) : result' unit :=
  let check_body (where_ : string) (t : EAst.term) : result' unit :=
    match unlowered_term t with
    | Some s =>
      Err ("The " ++ backend ++ " backend does not support " ++ s ++ ", used in " ++ where_ ++
           ". Enabling the implement_lazy phase in the configuration's erasure_phases translates them.")
    | None => Ok tt
    end in
  let check_decl (d : kername * EAst.global_decl) : result' unit :=
    match snd d with
    | EAst.ConstantDecl {| EAst.cst_body := Some t |} => check_body (string_of_kername (fst d)) t
    | _ => Ok tt
    end in
  monad_iter check_decl (fst p);;
  check_body "the main term" (snd p).

Definition check_lowered (c : config) (p : PAst) : result' unit :=
  let backend :=
    match c.(backend_opts) with
    | C _ => Some "C"
    | Wasm _ => Some "Wasm"
    | LLVM _ => Some "LLVM"
    | OCaml _ => Some "OCaml"
    | CakeML _ => Some "CakeML"
    | Eval _ => Some "eval"
    | Rust _ | Elm _ | Lean _ | FSharp _ | Koka _ | KokaTyped _ | AST _ => None
    end in
  match backend, p with
  | Some b, Untyped env (Some t) => check_lowered_program b (env, t)
  | Some b, Untyped env None => check_lowered_program b (env, EAst.tBox)
  | _, _ => Ok tt
  end.

(** [inline_recursors]: add the program's recursors ([I_rect]/[I_rec]) to the
    inlinings, as if an attribute file listing them had been passed
    (see RecursorInlining.v); the remapped ones are left to the remapping. *)
Definition peregrine_pipeline (c : string + config') (attrs : list string) (inline_recursors : bool)
  (lbox : lbox_opts) (p : string) (f : string) : extraction_result :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c attrs;; (* Parse or construct config *)
  let remapped kn := List.existsb (fun '(kn', _) => Kernames.eq_kername kn kn') c.(const_remappings_opts) in
  let c := if inline_recursors then merge_attributes_config c [recursor_attributes remapped p] else c in
  check_wf p;; (* Check that AST is wellformed *)
  NameSanitize.check_sanitized_injective (NameSanitize.get_sanitizer c)
    (List.app (NameSanitize.PAst_names p) (NameSanitize.config_names c));; (* Reject name collisions *)
  p <- NameSanitize.sanitize_PAst (NameSanitize.get_sanitizer c) p;; (* Sanitize names in AST *)
  c <- NameSanitize.sanitize_config (NameSanitize.get_sanitizer c) c;; (* Sanitize names in config *)
  p <- apply_transforms c lbox p (needs_typed c);; (* Apply program transformation *)
  check_lowered c p;; (* Reject terms that the backend would miscompile *)
  run_backend c f p. (* Run extraction backend *)

Definition peregrine_validate (c : string + config') (attrs : list string) (p : string) : result' unit :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c attrs;; (* Parse or construct config *)
  check_wf p. (* Check that AST is wellformed *)
