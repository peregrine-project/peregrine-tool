From Peregrine Require Import DeserializeCommon.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonSound.
From Peregrine Require Import DeserializePrimitives.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import SerializePrimitivesSound.
From Peregrine Require Import DeserializeEAst.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import CeresExtra.
From CeresBS Require Import Ceres.
From MetaRocq.Utils Require Import bytestring.
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



(* Helper lemmas for Term soundness proof *)

Lemma sound_class_list_def_strong {T : Set}
     `{Serialize T} `{Deserialize T}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : T), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (ts : list (def T)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr ts ->
    map to_sexp ts = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H1].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_def in Hdes.
  apply sound_match_con in Hdes.
  destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  destruct Ee as [es' [<- Ea]].
  sound_field Ea.
  apply sound_class in Ea1 as <-.
  apply sound_class in Ea2 as <-.
  inversion HPe as [|? HP_list Hss_inner]; subst.
  apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
  apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
  apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
  apply SoundClassStrong_implies_P in Hss_e.
  eapply HP in Hss_e as <-; eauto.
  cbn. reflexivity.
Qed.

Lemma sound_class_prim_val_strong {T : Set}
     `{Serialize T} `{Deserialize T}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : T), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall e l (p : EPrimitive.prim_val T),
    SoundClassStrong P e ->
    _from_sexp l e = inr p ->
    to_sexp p = e.
Proof.
  intros e l p Hss Hdes.
  destruct e; cbn in *; try discriminate.
  destruct xs as [|tag [|val [|]]]; try discriminate.
  destruct (_from_sexp _ tag) as [|tag'] eqn:Htag; try discriminate.
  apply sound_class in Htag as <-.
  destruct tag'.
  - (* Primitive Integers *)
    destruct _from_sexp as [|i] eqn:Hval; try discriminate.
    apply sound_class in Hval as <-.
    injection Hdes as <-; cbn.
    reflexivity.
  - (* Primitive Floats *)
    destruct _from_sexp as [|f] eqn:Hval; try discriminate.
    apply sound_class in Hval as <-.
    injection Hdes as <-; cbn.
    reflexivity.
  - (* Primitive Strings *)
    destruct _from_sexp as [|s] eqn:Hval; try discriminate.
    apply sound_class in Hval as <-.
    injection Hdes as <-; cbn.
    reflexivity.
  - (* Primitive Arrays *)
    destruct _from_sexp as [|a] eqn:Hval; try discriminate.
    injection Hdes as <-; cbn.
    inversion Hss as [|fields HP_list Hss_inner Heq]; subst.
    apply Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply Forall_cons_iff in Hss_inner as [Hss_val _].
    unfold _from_sexp, Deserialize_array_model in Hval.
    apply sound_match_con in Hval.
    destruct Hval as [Hval | Hval]; elim_Exists Hval.
    destruct Hval as [fields' [Heq' Hfields']].
    cbn in Heq'. inversion Heq'; subst.
    sound_field Hfields'.
    inversion Hss_val as [|fields'' HP_val Hss_val_inner Heq'']; subst.
    apply Forall_cons_iff in Hss_val_inner as [_ Hss_val_inner].
    apply Forall_cons_iff in Hss_val_inner as [Hss_default Hss_val_inner].
    apply Forall_cons_iff in Hss_val_inner as [Hss_values _].
    apply SoundClassStrong_implies_P in Hss_default.
    eapply HP in Hss_default; eauto.
    unfold to_sexp, Serialize_product.
    unfold to_sexp, Serialize_array_model; cbn.
    do 7 f_equal.
    + (* Array default element *)
      unfold to_sexp.
      exact Hss_default.
    + (* Array value *)
      clear dependent e.
      destruct e0; cbn in Ea0; try discriminate.
      apply SoundClassStrong_List_inv in Hss_values.
      eapply sound_class_list_forall in Ea0.
      * unfold to_sexp, Serialize_list, to_sexp.
        unfold to_sexp in Ea0.
        rewrite Ea0.
        reflexivity.
      * apply Forall_SoundClassStrong_Forall_P in Hss_values.
        eapply Forall_impl; eauto.
Qed.

(* Needed because destruct blows up in later proofs *)
Lemma sexp_inv : forall (e : sexp),
  (exists x, e = Atom_ x) \/ (exists x, e = List x).
Proof.
  intros.
  destruct e.
  - left.
    exists a.
    reflexivity.
  - right.
    exists xs.
    reflexivity.
Qed.



(* Term soundness proof *)

Definition SoundTerm : sexp -> Prop :=
  fun e =>
    forall l t,
      deserialize_term l e = inr t ->
        Serialize_term t = e.

Lemma SoundClassStrong_SoundTerm_sound :
  forall e,
    SoundClassStrong SoundTerm e ->
      SoundTerm e.
Proof.
  apply SoundClassStrong_implies_P.
Qed.

Lemma SoundClassStrong_SoundTerm_nested_strong :
  forall es,
    SoundClassStrong SoundTerm (List es) ->
      Forall (SoundClassStrong SoundTerm) es.
Proof.
  intros es Hss.
  apply SoundClassStrong_List_inv.
  assumption.
Qed.

#[bypass_check(guard)]
Lemma Sound_term_aux : SoundClass term.
Proof.
  unfold SoundClass, Sound.
  intros l e.
  generalize dependent l.
  apply SoundClassStrong_SoundTerm_sound.
  induction e as [a|es Hall];
    constructor; auto;
    intros l t He;
    unfold _from_sexp, Deserialize_term, deserialize_term in He;
    apply sound_match_con in He;
    destruct He as [He | He]; elim_Exists He;
      try (destruct He as [? [H ?]]; cbn in H; discriminate);
      try (now destruct He as [? ?]; discriminate);
      try fold deserialize_term in He.
  - (* tBox *)
    destruct He as [-> He]; subst; simpl.
    reflexivity.
  - (* tRel *)
    destruct He as [es' [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - (* tVar *)
    destruct He as [es' [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - (* tEvar *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].

    destruct (sexp_inv e0) as [[] | []]; subst; try discriminate.
    cbn.
    do 4 f_equal.
    eapply sound_class_list_forall in Ea0 as <-.
    reflexivity.
    unfold SoundTerm in H.
    apply SoundClassStrong_List_inv in H.
    eapply Forall_impl; eauto.
    intros ? Hss.
    apply SoundClassStrong_implies_P in Hss.
    exact Hss.
  - (* tLambda *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H); eauto.
    cbn.
    reflexivity.
  - (* tLetIn *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H1 Hall].
    apply Forall_cons_iff in Hall as [H2 _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H1); eauto.
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H2); eauto.
    cbn.
    reflexivity.
  - (* tApp *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H1 Hall].
    apply Forall_cons_iff in Hall as [H2 _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H1); eauto.
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H2); eauto.
    cbn.
    reflexivity.
  - (* tConst *)
    destruct He as [es' [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - (* tConstruct *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea0 as <-.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].

    destruct (sexp_inv e1) as [[] | []]; subst; try discriminate.
    cbn.
    do 5 f_equal.
    eapply sound_class_list_forall in Ea2 as <-.
    reflexivity.
    unfold SoundTerm in H.
    apply SoundClassStrong_List_inv in H.
    eapply Forall_impl; eauto.
    intros ? Hss.
    apply SoundClassStrong_implies_P in Hss.
    exact Hss.
  - (* tCase *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H1 Hall].
    apply Forall_cons_iff in Hall as [H2 _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H1); eauto.
    clear dependent e0.
    destruct e1; cbn in Ea2; try discriminate.
    apply SoundClassStrong_SoundTerm_nested_strong in H2.
    cbn.
    do 5 f_equal.
    eapply sound_class_list_prod_strong in Ea2; eauto.
    + unfold to_sexp, Serialize_product, to_sexp.
      unfold to_sexp, Serialize_product, to_sexp in Ea2.
      rewrite Ea2.
      reflexivity.
    + intros ? HP.
      exact HP.
  - (* tProj *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea1 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H); eauto.
    cbn.
    reflexivity.
  - (* tFix *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea0 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    destruct (sexp_inv e) as [[] | []]; subst; try discriminate.
    apply SoundClassStrong_SoundTerm_nested_strong in H.
    cbn.
    do 3 f_equal.
    unfold to_sexp; unfold Serialize_mfixpoint, to_sexp, Serialize_list.
    eapply sound_class_list_def_strong in Ea1 as <-; eauto.
    intros ? HP.
    exact HP.
  - (* tCoFix *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply sound_class in Ea0 as <-.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    destruct (sexp_inv e) as [[] | []]; subst; try discriminate.
    apply SoundClassStrong_SoundTerm_nested_strong in H.
    cbn.
    do 3 f_equal.
    unfold to_sexp; unfold Serialize_mfixpoint, to_sexp, Serialize_list.
    eapply sound_class_list_def_strong in Ea1 as <-; eauto.
    intros ? HP.
    exact HP.
  - (* tPrim *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    eapply sound_class_prim_val_strong in Ea1; eauto.
    cbn.
    do 3 f_equal.
    + exact Ea1.
    + intros ? HP.
      exact HP.
  - (* tLazy *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H); eauto.
    cbn.
    reflexivity.
  - (* tForce *)
    destruct He as [es' [H1 He]].
    cbn in H1; inversion H1; subst; clear H1.
    sound_field He.
    apply Forall_cons_iff in Hall as [_ Hall].
    apply Forall_cons_iff in Hall as [H _].
    erewrite <- (SoundClassStrong_SoundTerm_sound _ H); eauto.
    cbn.
    reflexivity.
Qed.

Instance Sound_term : SoundClass term := Sound_term_aux.

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
