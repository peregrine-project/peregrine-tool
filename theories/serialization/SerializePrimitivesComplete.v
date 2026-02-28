From Peregrine Require Import DeserializePrimitives.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import CeresExtra.
From CeresBS Require Import CeresRoundtrip.
From CeresBS Require Import CeresSerialize.
From CeresBS Require Import CeresDeserialize.
From MetaRocq.Common Require Import Primitive.
From MetaRocq.Erasure Require Import EPrimitive.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require PrimInt63.
From Stdlib Require PrimFloat.



(* TODO: validate axioms *)
Axiom prim_int_ser_complete : forall x, (prim_int_of_string (string_of_prim_int x)) = x.
Axiom prim_float_ser_complete : forall x, (prim_float_of_string (string_of_prim_float x)) = x.
Axiom prim_string_ser_complete : forall x, (prim_string_of_string (string_of_prim_string x)) = x.



Instance Complete_prim_tag : CompleteClass prim_tag.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  destruct x; reflexivity.
Qed.

Instance Complete_prim_int : CompleteClass PrimInt63.int.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  cbn.
  rewrite prim_int_ser_complete.
  reflexivity.
Qed.

Instance Complete_prim_float : CompleteClass PrimFloat.float.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  cbn.
  rewrite prim_float_ser_complete.
  reflexivity.
Qed.

Instance Complete_prim_string : CompleteClass PrimString.string.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  cbn.
  rewrite prim_string_ser_complete.
  reflexivity.
Qed.

Instance Complete_array_model {T : Set} `{CompleteClass T} : CompleteClass (array_model T).
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  cbn.
  simpl_bytes.
  rewrite complete_class.
  rewrite complete_class_list.
  destruct a; cbn.
  reflexivity.
Qed.

Instance Complete_prim_val {T : Set} `{CompleteClass T} : CompleteClass (prim_val T).
Proof.
  unfold CompleteClass, Complete.
  intros l p.
  destruct p.
  destruct p.
  - cbn -[Deserialize_prim_int].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[DeserializePrimitives.Deserialize_prim_float].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_prim_string].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_array_model].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.
