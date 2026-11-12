(** * A simulation relation for partial evaluation and call redirection

    This file provides the semantic core of the correctness proof of
    [EInstanceSpecialize]: a relation [G Σ Σ'] between a term of an environment
    [Σ] and a term of an environment [Σ'], which is preserved by weak
    call-by-value evaluation (with constructors as blocks, unguarded
    fixpoints).  [G Σ Σ' t u] holds when [u] is obtained from [t] by

    - contracting beta redexes whose argument is an arbitrary term
      ([Gs_beta]), iota redexes on a constructor with arbitrary arguments
      ([Gs_iota]) and unfolding an applied fixpoint ([Gs_fix_unfold]);
    - unfolding a constant of [Σ] ([Gs_unfold]) or folding a term into a
      constant of [Σ'] whose body it is related to ([G_fold]);
    - replacing a closed value by a closed term that evaluates to a related
      value ([G_val]): this is what makes contracting a redex with a non-value
      argument sound for a terminating source evaluation.

    [Gv] is the induced relation on values.  The main result is
    [G_simulation]; [gstage]/[gchain] package it for whole programs. *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv EWcbvEval EProgram EImplementBox.
From Peregrine Require Import ELiftConstants.
Import ListNotations.
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Local Existing Instance block_wcbv_flags.

Definition brs_rel (R : term -> term -> Prop) : list (list name × term) -> list (list name × term) -> Prop :=
  Forall2 (fun br br' => br.1 = br'.1 /\ R br.2 br'.2).

Definition fix_rel (R : term -> term -> Prop) : mfixpoint term -> mfixpoint term -> Prop :=
  Forall2 (fun d d' => dname d = dname d' /\ rarg d = rarg d' /\ R (dbody d) (dbody d')).

Section Rel.
  Variables Σ Σ' : global_declarations.

  Inductive Gs : term -> term -> Prop :=
  | Gs_box : Gs tBox tBox
  | Gs_rel n : Gs (tRel n) (tRel n)
  | Gs_var na : Gs (tVar na) (tVar na)
  | Gs_const kn : Gs (tConst kn) (tConst kn)
  | Gs_evar n ts ts' : Forall2 G ts ts' -> Gs (tEvar n ts) (tEvar n ts')
  | Gs_lambda na b b' : G b b' -> Gs (tLambda na b) (tLambda na b')
  | Gs_letin na v v' b b' : G v v' -> G b b' -> Gs (tLetIn na v b) (tLetIn na v' b')
  | Gs_app f f' a a' : G f f' -> G a a' -> Gs (tApp f a) (tApp f' a')
  | Gs_case ci d d' brs brs' : G d d' -> brs_rel G brs brs' -> Gs (tCase ci d brs) (tCase ci d' brs')
  | Gs_proj p u u' : G u u' -> Gs (tProj p u) (tProj p u')
  | Gs_fix mf mf' idx : fix_rel G mf mf' -> Gs (tFix mf idx) (tFix mf' idx)
  | Gs_cofix mf mf' idx : fix_rel G mf mf' -> Gs (tCoFix mf idx) (tCoFix mf' idx)
  | Gs_construct ind c args args' : Forall2 G args args' -> Gs (tConstruct ind c args) (tConstruct ind c args')
  | Gs_prim_int i : Gs (tPrim (prim_int i)) (tPrim (prim_int i))
  | Gs_prim_float f : Gs (tPrim (prim_float f)) (tPrim (prim_float f))
  | Gs_prim_string s : Gs (tPrim (prim_string s)) (tPrim (prim_string s))
  | Gs_prim_array d d' v v' :
      G d d' -> Forall2 G v v' ->
      Gs (tPrim (prim_array {| array_default := d; array_value := v |}))
         (tPrim (prim_array {| array_default := d'; array_value := v' |}))
  | Gs_lazy u u' : G u u' -> Gs (tLazy u) (tLazy u')
  | Gs_force u u' : G u u' -> Gs (tForce u) (tForce u')
  (* unfolding a source constant *)
  | Gs_unfold c decl b u :
      declared_constant Σ c decl -> cst_body decl = Some b -> closedn 0 u ->
      G b u -> Gs (tConst c) u
  (* beta with an arbitrary argument *)
  | Gs_beta f a na b' a' :
      G f (tLambda na b') -> G a a' -> Gs (tApp f a) (subst [a'] 0 b')
  (* unfolding an applied fixpoint *)
  | Gs_fix_unfold f a mfix' idx n fn' a' :
      G f (tFix mfix' idx) -> closedn 0 (tFix mfix' idx) ->
      cunfold_fix mfix' idx = Some (n, fn') -> G a a' ->
      Gs (tApp f a) (tApp fn' a')
  (* iota on a constructor with arbitrary arguments *)
  | Gs_iota ind npar d brs i c cargs' brs' br' :
      G d (tConstruct i c cargs') -> brs_rel G brs brs' ->
      nth_error brs' c = Some br' -> #|skipn npar cargs'| = #|br'.1| ->
      Gs (tCase (ind, npar) d brs) (subst (List.rev (skipn npar cargs')) 0 br'.2)

  with G : term -> term -> Prop :=
  | G_s t u : Gs t u -> G t u
  (* folding into a target constant *)
  | G_fold fn decl' b' t :
      declared_constant Σ' fn decl' -> cst_body decl' = Some b' -> closedn 0 t ->
      G t b' -> G t (tConst fn)
  (* a closed value against a closed term evaluating to a related value *)
  | G_val va a' va' :
      closedn 0 va -> closedn 0 a' -> ∥ eval Σ va va ∥ -> ∥ eval Σ' a' va' ∥ ->
      Gv va va' -> G va a'

  with Gv : term -> term -> Prop :=
  | Gv_box : Gv tBox tBox
  | Gv_lambda na b b' : G b b' -> Gv (tLambda na b) (tLambda na b')
  | Gv_fix mf mf' idx : fix_rel G mf mf' -> Gv (tFix mf idx) (tFix mf' idx)
  | Gv_cofix mf mf' idx : fix_rel G mf mf' -> Gv (tCoFix mf idx) (tCoFix mf' idx)
  | Gv_lazy u u' : G u u' -> Gv (tLazy u) (tLazy u')
  | Gv_prim_int i : Gv (tPrim (prim_int i)) (tPrim (prim_int i))
  | Gv_prim_float f : Gv (tPrim (prim_float f)) (tPrim (prim_float f))
  | Gv_prim_string s : Gv (tPrim (prim_string s)) (tPrim (prim_string s))
  | Gv_prim_array d d' v v' :
      Gv d d' -> Forall2 Gv v v' ->
      Gv (tPrim (prim_array {| array_default := d; array_value := v |}))
         (tPrim (prim_array {| array_default := d'; array_value := v' |}))
  | Gv_construct ind c args args' : Forall2 Gv args args' -> Gv (tConstruct ind c args) (tConstruct ind c args')
  | Gv_app f f' a a' : Gv f f' -> Gv a a' -> Gv (tApp f a) (tApp f' a').

  Lemma Gv_G v v' : Gv v v' -> G v v'.
  Proof.
    revert v v'. fix IH 3. intros v v' H.
    destruct H; apply G_s; try (constructor; auto; fail).
    - constructor; auto.
      revert v v' H0. fix aux 3. intros ? ? []; constructor; auto.
    - constructor.
      revert args args' H. fix aux 3. intros ? ? []; constructor; auto.
  Qed.

  Lemma Forall2_Gv_G l l' : Forall2 Gv l l' -> Forall2 G l l'.
  Proof. induction 1; constructor; auto using Gv_G. Qed.

  Lemma G_refl t : G t t.
  Proof.
    induction t using term_forall_list_ind; apply G_s; try now constructor.
    all: try (constructor; eauto; eapply All_Forall2_refl; tea; cbn; intuition eauto; fail).
    destruct p as [? []]; try constructor. depelim X. destruct p as [Hd Hv].
    destruct a; cbn in *. constructor; auto.
    eapply All_Forall2_refl; tea. auto.
  Qed.

  Lemma Forall2_G_refl l : Forall2 G l l.
  Proof. induction l; constructor; auto using G_refl. Qed.

  Lemma G_mkApps f f' args args' :
    G f f' -> Forall2 G args args' -> G (mkApps f args) (mkApps f' args').
  Proof.
    intros Hf H. induction H in f, f', Hf |- *; cbn; auto.
    apply IHForall2. now apply G_s; constructor.
  Qed.

  Definition closed_pres (t : term) := forall k u, closedn k t -> G t u -> closedn k u.

  Lemma closed_pres_list l l' k :
    All closed_pres l -> forallb (closedn k) l -> Forall2 G l l' -> forallb (closedn k) l'.
  Proof.
    intros X Hc H. induction H in X, Hc |- *; cbn in *; auto.
    depelim X. move/andP: Hc => [Hx Hl]. apply/andP; split; eauto.
  Qed.

  Lemma closed_pres_brs (l l' : list (list name × term)) k :
    All (fun x => closed_pres x.2) l ->
    forallb (fun br => closedn (#|br.1| + k) br.2) l -> brs_rel G l l' ->
    forallb (fun br => closedn (#|br.1| + k) br.2) l'.
  Proof.
    intros X Hc H. induction H in X, Hc |- *; cbn in *; auto.
    depelim X. move/andP: Hc => [Hx Hl]. destruct H as [e Hr]. apply/andP; split; eauto.
    rewrite -e. eauto.
  Qed.

  Lemma closed_pres_mfix (m m' : mfixpoint term) k :
    All (fun d => closed_pres (dbody d)) m ->
    forallb (test_def (closedn k)) m -> fix_rel G m m' ->
    forallb (test_def (closedn k)) m'.
  Proof.
    intros X Hc H. induction H in X, Hc |- *; cbn in *; auto.
    depelim X. move/andP: Hc => [Hx Hl]. destruct H as (? & ? & Hr). apply/andP; split; eauto.
  Qed.

  Lemma G_closed t : closed_pres t.
  Proof.
    induction t using term_forall_list_ind; intros k u Hc H;
      (inversion H as [? ? Hs | | ]; subst;
       [inversion Hs; subst | reflexivity | eapply closed_upwards; tea; lia ]).
    all: cbn in Hc |- *; rtoProp; auto.
    all: try (eapply closed_upwards; tea; lia).
    - eapply closed_pres_list; tea.
    - (* beta *)
      match goal with H : G t1 (tLambda _ _) |- _ => specialize (IHt1 _ _ H0 H); cbn in IHt1 end.
      eapply closedn_subst; cbn; rewrite ?andb_true_r; eauto.
    - (* fix unfold *)
      split; eauto. eapply closed_upwards; [eapply closed_cunfold_fix; tea|lia].
    - eapply closed_pres_list; tea.
    - split; eauto. eapply closed_pres_brs; tea.
    - (* iota *)
      match goal with H : G t (tConstruct _ _ _) |- _ => specialize (IHt _ _ H0 H); cbn in IHt end.
      match goal with H : brs_rel G _ _ |- _ => pose proof (closed_pres_brs _ _ _ X H1 H) as Hbrs end.
      eapply closedn_subst.
      + rewrite forallb_rev. now apply forallb_skipn.
      + rewrite List.length_rev. eapply (forallb_nth_error _ _ c) in Hbrs.
        rewrite H6 in Hbrs. cbn in Hbrs. rewrite H7. exact Hbrs.
    - match goal with H : fix_rel G _ _ |- _ => rewrite -(Forall2_length H); eapply closed_pres_mfix; tea end.
    - match goal with H : fix_rel G _ _ |- _ => rewrite -(Forall2_length H); eapply closed_pres_mfix; tea end.
    - depelim X. destruct p as [Hd Hv]. cbn in *. unfold test_array_model in *; cbn in *.
      rtoProp; split; eauto. eapply closed_pres_list; tea.
  Qed.

  Section Subst.
    Variables σ σ' : list term.
    Hypothesis Hσ : Forall2 G σ σ'.
    Hypothesis clσ : forallb (closedn 0) σ.
    Hypothesis clσ' : forallb (closedn 0) σ'.

    Definition subst_pres (t : term) := forall k u, G t u -> G (subst σ k t) (subst σ' k u).

    Lemma subst_pres_list l l' k :
      All subst_pres l -> Forall2 G l l' ->
      Forall2 G (map (subst σ k) l) (map (subst σ' k) l').
    Proof.
      intros X H. induction H in X |- *; cbn; constructor; depelim X; eauto.
    Qed.

    Lemma subst_pres_brs (l l' : list (list name × term)) k :
      All (fun x => subst_pres x.2) l -> brs_rel G l l' ->
      brs_rel G (map (fun br => (br.1, subst σ (#|br.1| + k) br.2)) l)
                (map (fun br => (br.1, subst σ' (#|br.1| + k) br.2)) l').
    Proof.
      intros X H. induction H as [|x y l l' [e Hr] H IH] in X |- *; cbn; constructor; depelim X.
      - cbn. split; auto. rewrite -e. now apply s.
      - now apply IH.
    Qed.

    Lemma subst_pres_mfix (m m' : mfixpoint term) k :
      All (fun d => subst_pres (dbody d)) m -> fix_rel G m m' ->
      fix_rel G (map (map_def (subst σ k)) m) (map (map_def (subst σ' k)) m').
    Proof.
      intros X H. induction H as [|x y l l' (e1 & e2 & Hr) H IH] in X |- *; cbn; constructor; depelim X.
      - cbn. repeat split; auto.
      - now apply IH.
    Qed.

    Lemma G_subst t : subst_pres t.
    Proof.
      induction t using term_forall_list_ind; intros k u H;
        (inversion H as [? ? Hs | ? ? ? ? ? ? Hcl | ? ? ? Hcl Hcl' ]; subst;
         [inversion Hs; subst
         | rewrite (subst_closed _ k _ (closed_upwards k Hcl ltac:(lia))); exact H
         | rewrite (subst_closed _ k _ (closed_upwards k Hcl ltac:(lia)))
                   (subst_closed _ k _ (closed_upwards k Hcl' ltac:(lia))); exact H ]).
      all: try (cbn; apply G_s; constructor; eauto; fail).
      - (* rel *)
        cbn. destruct (Nat.leb_spec k n); [|apply G_refl].
        destruct (nth_error σ (n - k)) eqn:e.
        + destruct (Forall2_nth_error_l _ _ _ _ _ Hσ e) as (t' & e' & Ht). rewrite e'.
          rewrite !lift_closed; auto.
          * pose proof (forallb_nth_error _ _ (n - k) clσ) as Hc. rewrite e in Hc. exact Hc.
          * pose proof (forallb_nth_error _ _ (n - k) clσ') as Hc. rewrite e' in Hc. exact Hc.
        + pose proof (Forall2_length Hσ) as el.
          apply nth_error_None in e. rewrite el in e. apply nth_error_None in e. rewrite e -el.
          apply G_refl.
      - cbn. apply G_s; constructor. now apply subst_pres_list.
      - (* beta *)
        rewrite distr_subst. cbn. apply G_s. eapply Gs_beta; eauto.
        match goal with H : G t1 (tLambda _ _) |- _ => apply (IHt1 k) in H; cbn in H; exact H end.
      - (* fix unfold *)
        cbn.
        pose proof H3 as Hfx; pose proof H4 as Hcu.
        assert (Hfn : closed fn') by (eapply closed_cunfold_fix; [exact Hfx|exact Hcu]).
        rewrite (subst_closed _ k fn' (closed_upwards k Hfn ltac:(lia))).
        apply G_s; eapply Gs_fix_unfold; [|exact Hfx|exact Hcu|eauto].
        match goal with H : G t1 (tFix _ _) |- _ =>
          apply (IHt1 k) in H; rewrite (subst_closed _ k _ (closed_upwards k Hfx ltac:(lia))) in H; exact H end.
      - (* unfold *)
        match goal with Hc : is_true (closed u) |- _ =>
          rewrite (subst_closed _ k _ (closed_upwards k Hc ltac:(lia))) end. exact H.
      - cbn. apply G_s; constructor. now apply subst_pres_list.
      - cbn. apply G_s; constructor; eauto. now apply subst_pres_brs.
      - (* iota *)
        rewrite distr_subst. cbn. rewrite map_rev map_skipn List.length_rev.
        match goal with e : #|skipn _ _| = #|_| |- _ => rewrite e end.
        apply G_s.
        eapply (Gs_iota _ _ _ _ _ _ _ _ (br'.1, subst σ' (#|br'.1| + k) br'.2)).
        + match goal with H : G t (tConstruct _ _ _) |- _ => apply (IHt k) in H; cbn in H; exact H end.
        + now apply subst_pres_brs.
        + rewrite nth_error_map. match goal with e : nth_error _ _ = Some _ |- _ => rewrite e end. reflexivity.
        + cbn. rewrite -map_skipn length_map. assumption.
      - cbn. apply G_s; constructor.
        match goal with H : fix_rel G _ _ |- _ => rewrite -(Forall2_length H) end. now apply subst_pres_mfix.
      - cbn. apply G_s; constructor.
        match goal with H : fix_rel G _ _ |- _ => rewrite -(Forall2_length H) end. now apply subst_pres_mfix.
      - depelim X. destruct p as [Hd Hv]. cbn in *. apply G_s; constructor; eauto.
        now apply subst_pres_list.
    Qed.
  End Subst.

End Rel.
