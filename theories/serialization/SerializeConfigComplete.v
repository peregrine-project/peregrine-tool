From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeConfig.
From Peregrine Require Import SerializeCommonComplete.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From Ceres Require Import Ceres.


Import ListNotations.
Local Open Scope bs_scope.



(** ** Backend Config *)


Instance Complete_rust_config : CompleteClass rust_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_rust_config' : CompleteClass rust_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_elm_config : CompleteClass elm_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_elm_config' : CompleteClass elm_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_certicoq_config : CompleteClass certicoq_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 5!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_certicoq_config' : CompleteClass certicoq_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident Deserialize_SemiIntegral Deserialize_option].
  rewrite !eqb_ascii_refl.
  rewrite 5!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_program_type : CompleteClass Serialize.program_type.
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  destruct a.
  - reflexivity.
  - cbn -[Deserialize_ident].
    rewrite !eqb_ascii_refl.
    rewrite 2!complete_class.
    reflexivity.
Qed.

Instance Complete_ocaml_config : CompleteClass ocaml_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_program_type].
  rewrite !eqb_ascii_refl.
  rewrite 1!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_ocaml_config' : CompleteClass ocaml_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_program_type].
  rewrite !eqb_ascii_refl.
  rewrite 1!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_backend_config : CompleteClass backend_config.
Proof.
  unfold CompleteClass, Complete.
  intros l b.
  destruct b.
  - cbn -[Deserialize_rust_config].
    rewrite !eqb_ascii_refl.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_elm_config].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_certicoq_config].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_certicoq_config].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_ocaml_config].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
Qed.

Instance Complete_backend_config' : CompleteClass backend_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l b.
  destruct b.
  - cbn -[Deserialize_rust_config'].
    rewrite !eqb_ascii_refl.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_elm_config'].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_certicoq_config'].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_certicoq_config'].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_ocaml_config'].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
Qed.



(** ** Config *)

Instance Complete_remapped_inductive : CompleteClass remapped_inductive.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_ident Deserialize_list Deserialize_option].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_external_remapping : CompleteClass external_remapping.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_inductive_mapping : CompleteClass EProgram.inductive_mapping.
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  destruct a, p.
  cbn -[Deserialize_ident Deserialize_list Deserialize_inductive].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  reflexivity.
Qed.

Instance Complete_remapping : CompleteClass remapping.
Proof.
  unfold CompleteClass, Complete.
  intros l r.
  destruct r.
  - cbn -[Deserialize_inductive Deserialize_external_remapping Deserialize_remapped_inductive].
    rewrite !eqb_ascii_refl.
    rewrite 3!complete_class.
    reflexivity.
  - cbn -[Deserialize_ident Deserialize_external_remapping Deserialize_kername Deserialize_option Deserialize_SemiIntegral Deserialize_bool].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite 5!complete_class.
    reflexivity.
  - cbn -[Deserialize_ident Deserialize_external_remapping Deserialize_kername Deserialize_option Deserialize_SemiIntegral Deserialize_bool].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite 5!complete_class.
    reflexivity.
Qed.

Instance Complete_custom_attribute : CompleteClass custom_attribute.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_inlinings : CompleteClass inlinings.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_remappings : CompleteClass remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_custom_attributes : CompleteClass custom_attributes.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_erasure_phases : CompleteClass erasure_phases.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_erasure_phases' : CompleteClass erasure_phases'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool].
  rewrite !eqb_ascii_refl.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_config : CompleteClass config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_backend_config Deserialize_erasure_phases Deserialize_option Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_remappings Deserialize_custom_attributes].
  rewrite !eqb_ascii_refl.
  rewrite 6!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_config' : CompleteClass config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_backend_config' Deserialize_erasure_phases' Deserialize_option Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_remappings Deserialize_custom_attributes].
  rewrite !eqb_ascii_refl.
  rewrite 6!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_attributes_config : CompleteClass attributes_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_remappings Deserialize_custom_attributes].
  rewrite !eqb_ascii_refl.
  rewrite 4!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.
