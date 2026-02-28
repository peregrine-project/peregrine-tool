From Peregrine Require Import DeserializeCommon.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonComplete.
From Peregrine Require Import DeserializePrimitives.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import SerializePrimitivesComplete.
From Peregrine Require Import DeserializeEAst.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import SerializeEAstComplete.
From Peregrine Require Import DeserializeExAst.
From Peregrine Require Import SerializeExAst.
From Peregrine Require Import CeresExtra.
From CeresBS Require Import CeresRoundtrip.
From CeresBS Require Import CeresSerialize.
From CeresBS Require Import CeresDeserialize.
From MetaRocq.Erasure Require Import ExAst.
From MetaRocq.Utils Require Import bytestring.
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
    simpl_bytes.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* TApp *)
    cbn.
    simpl_bytes.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* TVar *)
    cbn -[Deserialize_SemiIntegral].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - (* TInd *)
    cbn -[Deserialize_inductive].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - (* TConst *)
    cbn -[Deserialize_kername].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_type_var_info : CompleteClass type_var_info.
Proof.
  unfold CompleteClass, Complete.
  intros l t.
  cbn -[Deserialize_name Deserialize_bool].
  simpl_bytes.
  rewrite 4!complete_class.
  destruct t; cbn.
  reflexivity.
Qed.

Instance Complete_constant_body : CompleteClass constant_body.
Proof.
  unfold CompleteClass, Complete.
  intros l cb.
  cbn -[Deserialize_option].
  simpl_bytes.
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
  simpl_bytes.
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
  simpl_bytes.
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
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_mutual_inductive_body].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_option].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_global_env : CompleteClass global_env.
Proof.
  unfold CompleteClass, Complete.
  intros l gd.
  apply complete_class_list.
Qed.
