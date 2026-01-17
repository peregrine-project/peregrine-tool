From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonSound.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import SerializePrimitivesSound.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaRocq.Erasure Require Import EAst.
From Stdlib Require Import String.
From Stdlib Require Import List.



Instance Sound_def {T : Set} `{SoundClass T} : SoundClass (def T).
Proof.
  unfold SoundClass, Sound.
  intros l e d He.
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

Instance Sound_mfixpoint {T : Set} `{SoundClass T} : SoundClass (mfixpoint T).
Proof.
  unfold SoundClass, Sound.
  intros l e d He.
  destruct e; cbn in He; try discriminate.
  apply sound_class_list with (fs := nil) in He.
  assumption.
  reflexivity.
Qed.

Instance Sound_term : SoundClass term.
Proof.
  unfold SoundClass, Sound.
  intros l e t He.
  generalize dependent l.
  generalize dependent t.
  induction e using CeresS.sexp__ind; intros.
  - (* Atom constructors *)
    unfold _from_sexp, Deserialize_term, deserialize_term in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (destruct He as [? [H ?]]; cbn in H; discriminate).
    + (* tBox *)
      destruct He as [-> He]; subst; simpl.
      reflexivity.
  - (* List constructors *)
    unfold _from_sexp, Deserialize_term, deserialize_term in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (now destruct He as [? ?]; discriminate).
    + (* tRel *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tVar *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tEvar *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      admit.
    + (* tLambda *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      erewrite <- Ea1, <- H.
      reflexivity.
      eassumption.
    + (* tLetIn *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H1 H].
      apply List.Forall_cons_iff in H as [H0 _].
      erewrite <- Ea1, <- H1, <- H0.
      reflexivity.
      eassumption.
      eassumption.
    + (* tApp *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H1 H].
      apply List.Forall_cons_iff in H as [H0 _].
      erewrite <- H1, <- H0.
      reflexivity.
      eassumption.
      eassumption.
    + (* tConst *)
      destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tConstruct *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      apply sound_class in Ea1.
      rewrite <- Ea0; clear Ea0.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      admit.
    + (* tCase *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [He0 H].
      apply List.Forall_cons_iff in H as [He1 _].
      admit.
    + (* tProj *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      erewrite <- Ea1, <- H.
      reflexivity.
      eassumption.
    + (* tFix *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      rewrite <- Ea0; clear Ea0.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      admit.
    + (* tCoFix *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      rewrite <- Ea0; clear Ea0.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      admit.
    + (* tPrim *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      admit.
    + (* tLazy *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      erewrite <- H.
      reflexivity.
      eassumption.
    + (* tForce *)
      destruct He as [es [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      erewrite <- H.
      reflexivity.
      eassumption.
Admitted.

Instance Sound_constructor_body : SoundClass constructor_body.
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

Instance Sound_projection_body : SoundClass projection_body.
Proof.
  unfold SoundClass, Sound.
  intros l e pb He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  rewrite <- Ea1.
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
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
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

Instance Sound_constant_body : SoundClass constant_body.
Proof.
  unfold SoundClass, Sound.
  intros l e cb He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  rewrite <- Ea1.
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
Qed.

Instance Sound_global_declarations : SoundClass global_declarations.
Proof.
  unfold SoundClass, Sound.
  apply sound_class.
Qed.



Instance Sound_program : SoundClass program.
Proof.
  unfold SoundClass, Sound.
  apply SoundClass_prod.
Qed.
