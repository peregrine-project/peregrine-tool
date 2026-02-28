From Peregrine Require Import DeserializePrimitives.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import CeresExtra.
From CeresBS Require Import CeresRoundtrip.
From CeresBS Require Import CeresSerialize.
From CeresBS Require Import CeresDeserialize.
From MetaRocq.Common Require Import Primitive.
From MetaRocq.Erasure Require Import EPrimitive.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require PrimInt63.
From Stdlib Require PrimFloat.



(* TODO: validate axioms *)
Axiom prim_int_ser_sound : forall x, (string_of_prim_int (prim_int_of_string x)) = x.
Axiom prim_float_ser_sound : forall x, (string_of_prim_float (prim_float_of_string x)) = x.
Axiom prim_string_ser_sound : forall x, (string_of_prim_string (prim_string_of_string x)) = x.



Instance Sound_prim_tag : SoundClass prim_tag.
Proof.
  unfold SoundClass, Sound.
  intros l e t He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
Qed.

Instance Sound_prim_int : SoundClass PrimInt63.int.
Proof.
  unfold SoundClass, Sound.
  intros l e i He.
  destruct e; cbn in *; try discriminate.
  destruct a; cbn in *; try discriminate.
  injection He as <-.
  unfold to_sexp, Serialize_prim_int.
  rewrite prim_int_ser_sound.
  reflexivity.
Qed.

Instance Sound_prim_float : SoundClass PrimFloat.float.
Proof.
  unfold SoundClass, Sound.
  intros l e f He.
  destruct e; cbn in *; try discriminate.
  destruct a; cbn in *; try discriminate.
  injection He as <-.
  unfold to_sexp, SerializePrimitives.Serialize_prim_float.
  rewrite prim_float_ser_sound.
  reflexivity.
Qed.

Instance Sound_prim_string : SoundClass PrimString.string.
Proof.
  unfold SoundClass, Sound.
  intros l e f He.
  destruct e; cbn in *; try discriminate.
  destruct a; cbn in *; try discriminate.
  injection He as <-.
  unfold to_sexp, Serialize_prim_string.
  rewrite prim_string_ser_sound.
  reflexivity.
Qed.

Instance Sound_array_model {T : Set} `{SoundClass T} : SoundClass (array_model T).
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_array_model.
  cbn.
  rewrite Ea0, Ea1.
  reflexivity.
Qed.

Instance Sound_prim_val {T : Set} `{SoundClass T} : SoundClass (prim_val T).
Proof.
  unfold SoundClass, Sound.
  intros l e p He.
  destruct e; cbn in *; try discriminate.
  destruct xs; cbn in *; try discriminate.
  destruct xs; cbn in *; try discriminate.
  destruct xs; cbn in *; try discriminate.
  destruct _from_sexp eqn:Hs; try discriminate.
  apply sound_class in Hs.
  destruct p0.
  - destruct (_from_sexp l s0) eqn:Hs2; try discriminate.
    apply sound_class in Hs2.
    injection He as <-.
    rewrite <- Hs, <- Hs2.
    reflexivity.
  - destruct (_from_sexp l s0) eqn:Hs2; try discriminate.
    apply sound_class in Hs2.
    injection He as <-.
    rewrite <- Hs, <- Hs2.
    reflexivity.
  - destruct (_from_sexp l s0) eqn:Hs2; try discriminate.
    apply sound_class in Hs2.
    injection He as <-.
    rewrite <- Hs, <- Hs2.
    reflexivity.
  - destruct (_from_sexp l s0) eqn:Hs2; try discriminate.
    apply sound_class in Hs2.
    injection He as <-.
    rewrite <- Hs, <- Hs2.
    reflexivity.
Qed.
