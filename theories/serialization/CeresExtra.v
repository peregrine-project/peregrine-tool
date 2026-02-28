From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From CeresBS Require Import CeresUtils.
From CeresBS Require CeresParserUtils.
From CeresBS Require CeresString.
From MetaRocq.Utils Require All_Forall.

Import ListNotations.

Local Open Scope list_scope.

(* Completeness helper lemmas *)

Lemma complete_class_list_all {A : Type}
                             `{Serialize A}
                             `{Deserialize A} :
  forall (a xs : list A) (n : nat) (l : loc),
    All_Forall.All
      (fun t : A =>
       forall l : loc, _from_sexp l (to_sexp t) = inr t) a ->
    _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a).
Proof.
  induction a; intros; cbn.
  - rewrite rev_alt, app_nil_r.
    reflexivity.
  - inversion X; subst.
    rewrite H2.
    rewrite app_cons_assoc.
    apply IHa.
    assumption.
Qed.

Lemma complete_class_all_prod {A B : Type}
                             `{Serialize A}
                             `{Deserialize A}
                             `{Serialize B}
                             `{Deserialize B} :
  forall xs,
    CompleteClass A ->
    All_Forall.All
      (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp (snd x)) = inr (snd x)) xs ->
      All_Forall.All
        (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp x) = inr x) xs.
Proof.
  induction xs; intros.
  - apply All_Forall.All_nil.
  - apply All_Forall.All_cons.
    + intros.
      inversion X; subst.
      cbn.
      rewrite H5.
      rewrite complete_class.
      destruct a; cbn.
      reflexivity.
    + inversion X; subst.
      apply IHxs; assumption.
Qed.



(* Strong soundness *)

Inductive SoundClassStrong (P : sexp -> Prop) : sexp -> Prop :=
| SoundAtom : forall a,
    P (Atom a) ->
    SoundClassStrong P (Atom a)
| SoundList : forall es,
    P (List es) ->
    Forall (SoundClassStrong P) es ->
    SoundClassStrong P (List es).

Lemma SoundClassStrong_implies_P {P : sexp -> Prop} :
  forall e,
    SoundClassStrong P e -> P e.
Proof.
  intros e Hss.
  inversion Hss; auto.
Qed.

Lemma SoundClassStrong_List_inv {P : sexp -> Prop} :
  forall es,
    SoundClassStrong P (List es) ->
      Forall (SoundClassStrong P) es.
Proof.
  intros es Hss.
  inversion Hss; auto.
Qed.

Lemma Forall_SoundClassStrong_Forall_P {P : sexp -> Prop} :
  forall es,
    Forall (SoundClassStrong P) es ->
      Forall P es.
Proof.
  intros es Hss.
  induction Hss as [| e es' Hss_e Hss_es' IH]; constructor.
  - apply SoundClassStrong_implies_P.
    assumption.
  - assumption.
Qed.



(* Soundness helper lemmas *)

Local Lemma sound_class_list_forall_aux {A : Type}
                                 `{Serialize A}
                                 `{Deserialize A}
                                  (es : list sexp) :
  forall xs n l a,
    Forall (fun e => forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) es ->
    _sexp_to_list _from_sexp xs n l es = inr a ->
    map to_sexp a = (map to_sexp (rev xs) ++ es).
Proof.
  induction es as [| e es IH].
  - (* nil *)
    intros xs n l ts Hall Hdes.
    cbn in Hdes.
    injection Hdes as <-.
    rewrite rev_alt.
    rewrite app_nil_r.
    reflexivity.
  - (* cons *)
    intros xs n l ts Hall Hdes.
    cbn in Hdes.
    destruct (_from_sexp _ e) as [? | t] eqn:Hdes_e; try discriminate.
    inversion Hall as [|e' es' He Hes' Heq1]; subst.
    apply IH in Hdes; auto.
    rewrite Hdes; cbn.
    rewrite map_app; cbn.
    erewrite He; eauto.
    rewrite <- app_assoc; cbn.
    reflexivity.
Qed.

Lemma sound_class_list_forall {A : Type}
                             `{Serialize A}
                             `{Deserialize A}
                              (es : list sexp) :
  forall l (xs : list A),
    Forall (fun e => forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  erewrite sound_class_list_forall_aux; eauto.
  cbn.
  reflexivity.
Qed.

Lemma sound_class_list_strong {A : Type}
     `{Serialize A}
     `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es,
  Forall (SoundClassStrong P) es ->
  forall l xs,
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  erewrite sound_class_list_forall; eauto.
  apply Forall_SoundClassStrong_Forall_P in H1.
  eapply Forall_impl; [| exact H1].
  exact HP.
Qed.

Lemma sound_class_list_prod_strong {A B : Type}
     `{Serialize B} `{Deserialize B}
     `{SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (A * B)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map (fun p => List [to_sexp (fst p); to_sexp (snd p)]) xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H4].
  intros e HPe l' t Hdes.
  destruct t as [a b].
  unfold _from_sexp, Deserialize_prod in Hdes.
  destruct e; try discriminate.
  destruct xs0; try discriminate.
  destruct xs0; try discriminate.
  destruct xs0; try discriminate.
  destruct (_from_sexp _ s) eqn:Hdesa in Hdes; try discriminate.
  destruct (_from_sexp _ s0) eqn:Hdesb in Hdes; try discriminate.
  injection Hdes as <- <-.
  apply sound_class in Hdesa as <-.
  inversion HPe as [|? HP_list Hss_inner]; subst.
  apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
  apply List.Forall_cons_iff in Hss_inner as [Hss_b _].
  apply SoundClassStrong_implies_P in Hss_b.
  eapply HP in Hss_b as <-; eauto.
  cbn. reflexivity.
Qed.

Lemma sound_class_list_sum_strong {A B : Type}
     `{Serialize B} `{Deserialize B}
     `{SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (A + B)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H4].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_sum in Hdes.
  apply sound_match_con in Hdes.
  destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    apply sound_class in Ea1 as <-.
    cbn. reflexivity.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    inversion HPe as [|? HP_list Hss_inner]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
    apply SoundClassStrong_implies_P in Hss_e.
    eapply HP in Hss_e as <-; eauto.
    cbn. reflexivity.
Qed.

Lemma sound_class_list_option_strong {A : Type}
     `{Serialize A} `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (option A)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H1].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_option in Hdes.
  apply sound_match_con in Hdes.
  destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [E1 E2]; subst; reflexivity.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    inversion HPe as [|? HP_list Hss_inner]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
    apply SoundClassStrong_implies_P in Hss_e.
    eapply HP in Hss_e as <-; eauto.
    cbn. reflexivity.
Qed.

Lemma sound_class_list_list_strong {A : Type}
     `{Serialize A} `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (list A)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H1].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_list in Hdes.
  destruct e; try discriminate.
  unfold to_sexp, Serialize_list.
  erewrite sound_class_list_forall; eauto.
  apply SoundClassStrong_List_inv in HPe.
  eapply Forall_impl; [| exact HPe].
  intros e HPe' ? t' Hdes'.
  apply SoundClassStrong_implies_P in HPe'.
  eapply HP in HPe' as <-; eauto.
Qed.
