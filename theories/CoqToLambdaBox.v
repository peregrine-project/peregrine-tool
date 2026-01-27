From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Template Require Import Ast.
From MetaRocq.Template Require Import Loader.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.ErasurePlugin Require Import Loader.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import Extraction.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Peregrine Require SerializeEAst.
From Peregrine Require SerializeExAst.

Import MRMonadNotation.
Import ListNotations.



Program Definition cic_to_box p :=
  run_erase_program default_erasure_config ([], p) _.
Next Obligation.
  split. easy.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition cic_to_box_typed p :=
  entry <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  Ok Σ.


Definition serialize_box p :=
  SerializeEAst.string_of_program p.

Definition serialize_box_typed p :=
  SerializeExAst.string_of_global_env p.

Definition erase_untyped' p :=
  serialize_box (cic_to_box p).

Definition erase_typed' p :=
  match cic_to_box_typed p with
  | Ok p => serialize_box_typed p
  | Err e => e
  end.

From MetaRocq.Template Require Import TemplateMonad.

Definition erase_untyped {A : Type} (p : A) : TemplateMonad _ :=
t <- tmQuoteRecTransp p false ;;
let s := erase_untyped' t in
tmMsg s.

Definition erase_typed {A : Type} (p : A) : TemplateMonad _ :=
t <- tmQuoteRecTransp p false ;;
let s := erase_typed' t in
tmMsg s.


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
