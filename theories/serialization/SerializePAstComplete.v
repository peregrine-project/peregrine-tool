From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import PAst.
From Peregrine Require Import DeserializePAst.
From Peregrine Require Import SerializePAst.
From Peregrine Require Import SerializeEAstComplete.
From Peregrine Require Import SerializeExAstComplete.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(* Completeness *)

Instance Complete_typed_env : CompleteClass typed_env.
Proof. typeclasses eauto. Qed.

Instance Complete_untyped_env : CompleteClass untyped_env.
Proof. typeclasses eauto. Qed.

Instance Complete_PAst : CompleteClass PAst.
Proof.
  unfold CompleteClass, Complete.
  intros l n.
  destruct n.
  - cbn -[Deserialize_untyped_env Deserialize_option].
    simpl_bytes.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_typed_env Deserialize_option].
    simpl_bytes.
    rewrite !complete_class.
    reflexivity.
Qed.
