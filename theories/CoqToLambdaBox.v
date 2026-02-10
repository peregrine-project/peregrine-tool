From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Template Require Import Ast.
From MetaRocq.Template Require Import Loader.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Peregrine Require SerializeEAst.
From Peregrine Require SerializeExAst.
From Peregrine Require SerializePAst.
From Peregrine Require Erasure.
From Peregrine Require ErasureTyped.
From Peregrine Require Import PAst.

Import MRMonadNotation.
Import ListNotations.



Definition serialize_box p :=
  SerializeEAst.string_of_program p.

Definition serialize_box_typed p :=
  SerializeExAst.string_of_global_env p.

Definition serialize_past p :=
  SerializePAst.string_of_PAst p.


Definition erase_untyped_past p : PAst :=
  let (env, t) := Erasure.run_erase_only p in
  Untyped env (Some t).

Definition erase_typed_past p : PAst :=
  let (env, t) := ErasureTyped.run_typed_erase_only p in
  Typed env (Some t).


Definition erase_untyped' p :=
  serialize_past (erase_untyped_past p).

Definition erase_typed' p :=
  serialize_past (erase_typed_past p).


From MetaRocq.Template Require Import TemplateMonad.

Definition erase_untyped {A : Type} (p : A) : TemplateMonad _ :=
t <- tmQuoteRecTransp p false ;;
let s := erase_untyped' t in
tmMsg s.

Definition erase_typed {A : Type} (p : A) : TemplateMonad _ :=
t <- tmQuoteRecTransp p false ;;
let s := erase_typed' t in
tmMsg s.



(* * Rocq to lambdabox erasure example *)

(* Example term *)
(* Definition t (X : Type) (x : X) := x. *)

(* Erase and serialize untyped AST *)
(* MetaRocq Run (erase_untyped t). *)

(* Erase and serialize typed AST *)
(* MetaRocq Run (erase_typed t). *)

(* Translate Rocq def -> lambda_cic *)
(* MetaRocq Quote Recursively Definition ex1 := t. *)

(* Translate lambda_cic -> lambda_box *)
(* Eval vm_compute in cic_to_box ex1. *)

(* Translate lambda_cic -> lambda_boxtyped *)
(* Note that this only translates the environment *)
(* Eval vm_compute in cic_to_box_typed ex1. *)
