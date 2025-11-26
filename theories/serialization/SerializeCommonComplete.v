From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Universes.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import String.



Instance Complete_ident : CompleteClass ident.
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  cbn.
  rewrite bytestring_complete.
  reflexivity.
Qed.

Instance Complete_dirpath : CompleteClass dirpath.
Proof.
  unfold CompleteClass, Complete.
  intros l d.
  cbn.
  apply complete_class_list.
Qed.

Instance Complete_modpath : CompleteClass modpath.
Proof.
  unfold CompleteClass, Complete.
  intros l m.
  revert l.
  induction m; intros l.
  - cbn -[Deserialize_dirpath].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_dirpath Deserialize_ident Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite !complete_class.
    reflexivity.
  - cbn -[Deserialize_ident].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite IHm.
    rewrite !complete_class.
    reflexivity.
Qed.

Instance Complete_kername : CompleteClass kername.
Proof.
  unfold CompleteClass, Complete.
  intros l kn.
  rewrite complete_class.
  reflexivity.
Qed.

Instance Complete_inductive : CompleteClass inductive.
Proof.
  unfold CompleteClass, Complete.
  intros l ind.
  cbn -[Deserialize_kername Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 2!complete_class.
  destruct ind; cbn.
  reflexivity.
Qed.

Instance Complete_projection : CompleteClass projection.
Proof.
  unfold CompleteClass, Complete.
  intros l proj.
  cbn -[Deserialize_inductive Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  destruct proj; cbn.
  reflexivity.
Qed.



Instance Complete_name : CompleteClass name.
Proof.
  unfold CompleteClass, Complete.
  intros l n.
  destruct n.
  - reflexivity.
  - cbn -[Deserialize_ident].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_recursivity_kind : CompleteClass recursivity_kind.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  destruct x; reflexivity.
Qed.



Instance Complete_allowed_eliminations : CompleteClass allowed_eliminations.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  destruct x; reflexivity.
Qed.
