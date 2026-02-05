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

(** The soundness property for terms *)
Definition SoundTerm_P : sexp -> Prop :=
  fun e => forall l t, deserialize_term l e = inr t -> Serialize_term t = e.

(** Helper to extract soundness from StrongSound *)
Lemma StrongSound_SoundTerm_P_sound : forall e,
  StrongSound SoundTerm_P e -> SoundTerm_P e.
Proof.
  apply StrongSound_implies_P.
Qed.

(** For list elements that are Lists, extract the nested Forall *)
Lemma StrongSound_SoundTerm_P_nested : forall es,
  StrongSound SoundTerm_P (List es) -> Forall SoundTerm_P es.
Proof.
  apply StrongSound_List_extract_forall.
Qed.

(** Extract Forall (StrongSound SoundTerm_P) from StrongSound for a List *)
Lemma StrongSound_SoundTerm_P_nested_strong : forall es,
  StrongSound SoundTerm_P (List es) -> Forall (StrongSound SoundTerm_P) es.
Proof.
  intros es Hss.
  apply StrongSound_List_inv. assumption.
Qed.

(** Main lemma: all sexps satisfy StrongSound SoundTerm_P *)
Lemma StrongSound_term : forall e, StrongSound SoundTerm_P e.
Proof.
  apply StrongSound_from_sexp_ind.
  - (* Atom case *)
    intros a l t He.
    unfold _from_sexp, Deserialize_term, deserialize_term in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (destruct He as [? [H ?]]; cbn in H; discriminate).
    + (* tBox *)
      destruct He as [-> He]; subst; simpl.
      reflexivity.
  - (* List case *)
    intros es Hforall l t He.
    unfold _from_sexp, Deserialize_term, deserialize_term in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He;
      try (now destruct He as [? ?]; discriminate).
    + (* tRel *)
      destruct He as [es' [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tVar *)
      destruct He as [es' [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tEvar *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hlist _].
      (* Hlist : SoundTerm_P (List term_sexps) - but we need Forall for the inner list *)
      (* The sexp is List [Atom "tEvar"; n_sexp; List term_sexps] *)
      (* We need the inner Forall for term_sexps *)
      (* The deserialized list field is in e0 *)
      (* We need to show: List (map Serialize_term a0) = e0 *)
      (* where a0 is the deserialized list of terms and e0 is the List sexp *)
      (* Use sound_list_from_forall with the nested Forall *)
      destruct e0; cbn in Ea0; try discriminate.
      apply sound_list_from_forall_nil with (l := 2 :: l) in Ea0.
      * rewrite Ea0. reflexivity.
      * apply StrongSound_SoundTerm_P_nested. assumption.
    + (* tLambda *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm _].
      erewrite <- Ea1, <- (StrongSound_SoundTerm_P_sound _ Hterm).
      reflexivity.
      eassumption.
    + (* tLetIn *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm1 Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm0 _].
      erewrite <- Ea1, <- (StrongSound_SoundTerm_P_sound _ Hterm1), <- (StrongSound_SoundTerm_P_sound _ Hterm0).
      reflexivity.
      eassumption.
      eassumption.
    + (* tApp *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm1 Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm0 _].
      erewrite <- (StrongSound_SoundTerm_P_sound _ Hterm1), <- (StrongSound_SoundTerm_P_sound _ Hterm0).
      reflexivity.
      eassumption.
      eassumption.
    + (* tConst *)
      destruct He as [es' [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1.
      reflexivity.
    + (* tConstruct *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      apply sound_class in Ea1.
      rewrite <- Ea0; clear Ea0.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hlist _].
      destruct e2; cbn in Ea2; try discriminate.
      apply sound_list_from_forall_nil with (l := 3 :: l) in Ea2.
      * rewrite Ea2. reflexivity.
      * apply StrongSound_SoundTerm_P_nested. assumption.
    + (* tCase *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      rewrite <- Ea1; clear Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm Hforall].
      apply List.Forall_cons_iff in Hforall as [Hbranches _].
      (* Scrutinee: use StrongSound_SoundTerm_P_sound *)
      erewrite <- (StrongSound_SoundTerm_P_sound _ Hterm); [|eassumption].
      (* Branches: List of (list name * term) *)
      (* Hbranches : StrongSound SoundTerm_P (List branches_sexps) *)
      destruct e2; cbn in Ea2; try discriminate.
      (* e2 = List xs where xs are the branch sexps *)
      (* Each branch sexp is a List [names_sexp; term_sexp] *)
      (* Use sound_prod_list_from_strong_nil with StrongSound *)
      apply StrongSound_SoundTerm_P_nested_strong in Hbranches.
      (* Hbranches : Forall (StrongSound SoundTerm_P) xs *)
      erewrite (sound_prod_list_from_strong_nil
                  (fun names => to_sexp names) _from_sexp
                  Serialize_term deserialize_term
                  _ SoundTerm_P _ xs (3 :: l) a2 Hbranches Ea2).
      reflexivity.
      Unshelve.
      (* Need to show: forall e, SoundTerm_P e -> soundness for term deserialization *)
      intros e HP l' t Hdes.
      apply HP. assumption.
    + (* tProj *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea1.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm _].
      erewrite <- Ea1, <- (StrongSound_SoundTerm_P_sound _ Hterm).
      reflexivity.
      eassumption.
    + (* tFix *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      rewrite <- Ea0; clear Ea0.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hmfix _].
      (* Hmfix : StrongSound SoundTerm_P (List mfix_sexps) *)
      (* mfixpoint is list (def term), deserialized as List *)
      destruct e1; cbn in Ea1; try discriminate.
      apply StrongSound_SoundTerm_P_nested_strong in Hmfix.
      (* Hmfix : Forall (StrongSound SoundTerm_P) xs *)
      erewrite (sound_def_list_from_strong_nil
                  Serialize_term deserialize_term
                  SoundTerm_P _ xs (1 :: l) a1 Hmfix Ea1).
      reflexivity.
      Unshelve.
      intros e HP l' t Hdes. apply HP. assumption.
    + (* tCoFix *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      rewrite <- Ea0; clear Ea0.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hmfix _].
      destruct e1; cbn in Ea1; try discriminate.
      apply StrongSound_SoundTerm_P_nested_strong in Hmfix.
      erewrite (sound_def_list_from_strong_nil
                  Serialize_term deserialize_term
                  SoundTerm_P _ xs (1 :: l) a1 Hmfix Ea1).
      reflexivity.
      Unshelve.
      intros e HP l' t Hdes. apply HP. assumption.
    + (* tPrim *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hprim _].
      (* Hprim : StrongSound SoundTerm_P e0 (the prim sexp) *)
      (* Use sound_prim_val_from_strong *)
      erewrite (sound_prim_val_from_strong
                  Serialize_term deserialize_term
                  SoundTerm_P _ e0 (1 :: l) a0 Hprim Ea0).
      reflexivity.
      Unshelve.
      intros e' HP l' t' Hdes'. apply HP. assumption.
    + (* tLazy *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm _].
      erewrite <- (StrongSound_SoundTerm_P_sound _ Hterm).
      reflexivity.
      eassumption.
    + (* tForce *)
      destruct He as [es' [H1 He]].
      cbn in H1; inversion H1; subst; clear H1.
      sound_field He.
      apply List.Forall_cons_iff in Hforall as [_ Hforall].
      apply List.Forall_cons_iff in Hforall as [Hterm _].
      erewrite <- (StrongSound_SoundTerm_P_sound _ Hterm).
      reflexivity.
      eassumption.
Qed.

Instance Sound_term : SoundClass term.
Proof.
  unfold SoundClass, Sound.
  intros l e t He.
  apply (StrongSound_SoundTerm_P_sound e).
  apply StrongSound_term.
  assumption.
Qed.

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
