From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Utils Require Import bytestring.



Definition typed_env := ExAst.global_env.
Definition untyped_env := EAst.global_context.

Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed : typed_env -> option EAst.term -> PAst.



Definition PAst_to_EAst (ast : PAst) : result EAst.program string :=
  match ast with
  | Untyped env (Some t) => Ok (env, t)
  | Untyped env None => Ok (env, EAst.tBox) (* TODO: what should we in this case? *)
  | Typed env (Some t) => Ok (ExAst.trans_env env, t)
  | Typed env None => Ok (ExAst.trans_env env, EAst.tBox)
  end.

Definition PAst_to_ExAst (ast : PAst) : result ExAst.global_env string :=
  match ast with
  (* TODO: fix once we have type inference *)
  | Untyped env _ => Err "Cannot convert untyped program to a typed program"%bs
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
