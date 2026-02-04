From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeConfig.
From Peregrine Require Import SerializeCommonSound.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From Ceres Require Import Ceres.


Import ListNotations.
Local Open Scope bs_scope.



(** ** Backend Config *)

Instance Sound_rust_config : SoundClass rust_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_rust_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_rust_config' : SoundClass rust_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_rust_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_elm_config : SoundClass elm_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_elm_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_elm_config' : SoundClass elm_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_elm_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_certicoq_config : SoundClass certicoq_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  unfold to_sexp, Serialize_certicoq_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  reflexivity.
Qed.

Instance Sound_certicoq_config' : SoundClass certicoq_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  unfold to_sexp, Serialize_certicoq_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  reflexivity.
Qed.

Instance Sound_program_type : SoundClass Serialize.program_type.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    cbn.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    cbn.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
Qed.

Instance Sound_ocaml_config : SoundClass ocaml_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_ocaml_config.
  cbn.
  rewrite <- Ea1.
  reflexivity.
Qed.

Instance Sound_ocaml_config' : SoundClass ocaml_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_ocaml_config'.
  cbn.
  rewrite <- Ea1.
  reflexivity.
Qed.

Instance Sound_backend_config : SoundClass backend_config.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.

Instance Sound_backend_config' : SoundClass backend_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.



(** ** Config *)

Instance Sound_remapped_inductive : SoundClass remapped_inductive.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_remapped_inductive.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_external_remapping : SoundClass external_remapping.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_inductive_mapping : SoundClass EProgram.inductive_mapping.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  destruct a, p.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_inductive_mapping.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_remapping : SoundClass remapping.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    apply sound_class in Ea2.
    rewrite <- Ea0, <- Ea1, <- Ea2.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    apply sound_class in Ea2.
    apply sound_class in Ea3.
    apply sound_class in Ea4.
    rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    apply sound_class in Ea2.
    apply sound_class in Ea3.
    apply sound_class in Ea4.
    rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
    reflexivity.
Qed.

Instance Sound_custom_attribute : SoundClass custom_attribute.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_inlinings : SoundClass inlinings.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_remappings : SoundClass remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_custom_attributes : SoundClass custom_attributes.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_erasure_phases : SoundClass erasure_phases.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  unfold to_sexp, Serialize_erasure_phases.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  reflexivity.
Qed.

Instance Sound_erasure_config : SoundClass erasure_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_erasure_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_erasure_config' : SoundClass erasure_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_erasure_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_config : SoundClass config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  unfold to_sexp, Serialize_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5.
  reflexivity.
Qed.

Instance Sound_config' : SoundClass config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  unfold to_sexp, Serialize_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5.
  reflexivity.
Qed.
