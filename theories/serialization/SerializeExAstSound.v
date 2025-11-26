From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import SerializeCommonSound.
From LambdaBox Require Import SerializePrimitives.
From LambdaBox Require Import SerializePrimitivesSound.
From LambdaBox Require Import SerializeEAst.
From LambdaBox Require Import SerializeEAstSound.
From LambdaBox Require Import SerializeExAst.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaRocq.Erasure Require Import ExAst.
From Stdlib Require Import String.
From Stdlib Require Import List.



Instance Sound_box_type : SoundClass box_type.
Proof.
  unfold SoundClass, Sound.
  intros l e bt He.
  generalize dependent l.
  generalize dependent bt.
  induction e; intros.
  - (* Atom constructors *)
    unfold _from_sexp, Deserialize_box_type in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (now destruct He as [? [? ?]]; discriminate).
    + (* TBox *)
      destruct He as [-> He]; subst; simpl.
      reflexivity.
    + (* TAny *)
      destruct He as [-> He]; subst; simpl.
      reflexivity.
  - (* List constructors *)
    unfold _from_sexp, Deserialize_box_type in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (now destruct He as [? ?]; discriminate).
    + (* TArr *)
      destruct He as [es [H1 He]].
      inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H1 H].
      apply List.Forall_cons_iff in H as [H0 _].
      erewrite <- H1, <- H0.
      reflexivity.
      eassumption.
      eassumption.
    + (* TApp *)
      destruct He as [es [H1 He]].
      inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H1 H].
      apply List.Forall_cons_iff in H as [H0 _].
      erewrite <- H1, <- H0.
      reflexivity.
      eassumption.
      eassumption.
    + (* TVar *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* TInd *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* TConst *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
Qed.

Instance Sound_type_var_info : SoundClass type_var_info.
Proof.
  unfold SoundClass, Sound.
  intros l e tv He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3.
  reflexivity.
Qed.

Instance Sound_constant_body : SoundClass constant_body.
Proof.
  unfold SoundClass, Sound.
  intros l e cb He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  rewrite <- Ea0, <- Ea1.
  reflexivity.
Qed.

Instance Sound_one_inductive_body : SoundClass one_inductive_body.
Proof.
  unfold SoundClass, Sound.
  intros l e oib He.
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
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5.
  reflexivity.
Qed.

Instance Sound_mutual_inductive_body : SoundClass mutual_inductive_body.
Proof.
  unfold SoundClass, Sound.
  intros l e mib He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_global_decl : SoundClass global_decl.
Proof.
  unfold SoundClass, Sound.
  intros l e gd He.
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
Qed.

Instance Sound_global_env : SoundClass global_env.
Proof.
  unfold SoundClass, Sound.
  apply sound_class.
Qed.
