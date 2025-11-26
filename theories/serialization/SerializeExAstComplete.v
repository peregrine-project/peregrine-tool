From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import SerializeCommonComplete.
From LambdaBox Require Import SerializePrimitives.
From LambdaBox Require Import SerializePrimitivesComplete.
From LambdaBox Require Import SerializeEAst.
From LambdaBox Require Import SerializeEAstComplete.
From LambdaBox Require Import SerializeExAst.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaRocq.Erasure Require Import ExAst.
From Stdlib Require Import String.
From Stdlib Require Import List.



Instance Complete_box_type : CompleteClass box_type.
Proof.
  unfold CompleteClass, Complete.
  intros l t.
  revert l.
  induction t; intros l.
  - (* TBox *)
    reflexivity.
  - (* TAny *)
    reflexivity.
  - (* TArr *)
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* TApp *)
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* TVar *)
    cbn -[Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - (* TInd *)
    cbn -[Deserialize_inductive].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - (* TConst *)
    cbn -[Deserialize_kername].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_type_var_info : CompleteClass type_var_info.
Proof.
  unfold CompleteClass, Complete.
  intros l t.
  cbn -[Deserialize_name Deserialize_bool].
  rewrite !eqb_ascii_refl.
  rewrite 4!complete_class.
  destruct t; cbn.
  reflexivity.
Qed.

Instance Complete_constant_body : CompleteClass constant_body.
Proof.
  unfold CompleteClass, Complete.
  intros l cb.
  cbn -[Deserialize_option].
  rewrite !eqb_ascii_refl.
  rewrite 2!complete_class.
  rewrite complete_class_list.
  destruct cb, cst_type; cbn.
  reflexivity.
Qed.

Instance Complete_one_inductive_body : CompleteClass one_inductive_body.
Proof.
  unfold CompleteClass, Complete.
  intros l oib.
  cbn -[Deserialize_ident Deserialize_bool Deserialize_allowed_eliminations].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  rewrite 3!complete_class_list.
  destruct oib; cbn.
  reflexivity.
Qed.

Instance Complete_mutual_inductive_body : CompleteClass mutual_inductive_body.
Proof.
  unfold CompleteClass, Complete.
  intros l mib.
  cbn -[Deserialize_recursivity_kind Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 2!complete_class.
  rewrite complete_class_list.
  destruct mib; cbn.
  reflexivity.
Qed.

Instance Complete_global_decl : CompleteClass global_decl.
Proof.
  unfold CompleteClass, Complete.
  intros l gd.
  destruct gd.
  - cbn -[Deserialize_constant_body].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_mutual_inductive_body].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_option].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_global_env : CompleteClass global_env.
Proof.
  unfold CompleteClass, Complete.
  intros l gd.
  apply complete_class_list.
Qed.
