From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import PAst.
From Peregrine Require Import DeserializePAst.
From Peregrine Require Import SerializePAst.
From Peregrine Require Import DeserializeEAst.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import DeserializeExAst.
From Peregrine Require Import SerializeExAst.
From Peregrine Require Import SerializeEAstSound.
From Peregrine Require Import SerializeExAstSound.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.



(* Soundness *)

Instance Sound_typed_env : SoundClass typed_env.
Proof. typeclasses eauto. Qed.

Instance Sound_untyped_env : SoundClass untyped_env.
Proof. typeclasses eauto. Qed.

Instance Sound_PAst : SoundClass PAst.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    apply sound_class in Ea0.
    cbn.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    apply sound_class in Ea0.
    cbn.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
Qed.
