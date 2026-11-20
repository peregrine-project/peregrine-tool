From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Utils.
From Peregrine Require Import EHindleyMilner.

Local Open Scope bs_scope.



Definition typed_env := ExAst.global_env.
Definition untyped_env := EAst.global_context.

Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed : typed_env -> option EAst.term -> PAst.



(** The main term of a program without one: the identity function, a
    closed value that every transformation and every backend check accepts.
    (A [tBox] placeholder is rejected by the well-formedness checks of the
    OCaml and CakeML backends, for which boxes are implemented away.) *)
Definition no_main_term : EAst.term := EAst.tLambda BasicAst.nAnon (EAst.tRel 0).

(** [PAst_to_EAst_main m] uses [m] as the main term of a program without one. *)
Definition PAst_to_EAst_main (no_main : EAst.term) (ast : PAst) : result' EAst.program :=
  match ast with
  | Untyped env (Some t) => Ok (env, t)
  | Untyped env None => Ok (env, no_main)
  | Typed env (Some t) => Ok (ExAst.trans_env env, t)
  | Typed env None => Ok (ExAst.trans_env env, no_main)
  end.

Definition PAst_to_EAst : PAst -> result' EAst.program := PAst_to_EAst_main no_main_term.

(** The CertiRocq backends (C, Wasm, LLVM, the lambda-ANF AST output) keep
    [tBox] as the main term of a program without one: they compile a [tBox]
    main to box ([CertiRocqBackend.implement_main_box] in CPS mode). *)
Definition PAst_to_EAst_box : PAst -> result' EAst.program := PAst_to_EAst_main EAst.tBox.

(** Untyped (lambda-box) input for a typed target: annotate it by the
    Hindley-Milner inference [EHindleyMilner.infer], or fail with the
    inference's message.  Only [infer env = Ok env' -> trans_env env' = env]
    is proved ([EHindleyMilner.infer_section]): erasure recovers the original
    program.  The inferred [box_type] annotations are unverified. *)
Definition infer_for_backend (env : untyped_env) : result' typed_env :=
  map_error (fun e => "Could not infer types for the untyped input: " ++ e
                      ++ ". Provide a typed (lambda-box-typed) program.")
            (infer env).

Definition PAst_to_ExAst (ast : PAst) : result' ExAst.global_env :=
  match ast with
  (* [peregrine_pipeline] does not reach this case: for a typed target
     [Pipeline.apply_transforms] has already run [infer_for_backend]. *)
  | Untyped env _ => infer_for_backend env
  | Typed env (Some t) => Ok env (* TODO: add t to env, with a fresh name or hardcoded main? *)
  | Typed env None => Ok env
  end.

Definition is_typed_ast (p : PAst) : bool :=
  match p with
  | Untyped _ _ => false
  | Typed _ _ => true
  end.

Definition is_untyped_ast (p : PAst) : bool :=
  match p with
  | Untyped _ _ => true
  | Typed _ _ => false
  end.
