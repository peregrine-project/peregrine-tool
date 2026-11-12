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

  Lemma G_subst0 σ σ' t u :
    Forall2 G σ σ' -> forallb (closedn 0) σ -> forallb (closedn 0) σ' ->
    G t u -> G (subst σ 0 t) (subst σ' 0 u).
  Proof. intros. now apply G_subst. Qed.

  Lemma G_csubst a a' b b' :
    G a a' -> closedn 0 a -> closedn 0 a' -> G b b' -> G (csubst a 0 b) (csubst a' 0 b').
  Proof.
    intros Ha Hc Hc' Hb. rewrite !closed_subst //.
    apply G_subst0; auto; cbn; rewrite ?Hc ?Hc' //.
  Qed.

  Lemma G_substl σ σ' t u :
    Forall2 G σ σ' -> forallb (closedn 0) σ -> forallb (closedn 0) σ' ->
    G t u -> G (substl σ t) (substl σ' u).
  Proof. intros. rewrite !substl_subst //. now apply G_subst0. Qed.

  Lemma G_fix_subst mf mf' : fix_rel G mf mf' -> Forall2 G (fix_subst mf) (fix_subst mf').
  Proof.
    intros H. unfold fix_subst. rewrite (Forall2_length H).
    induction #|mf'|; constructor; auto. apply G_s. now constructor.
  Qed.

  Lemma G_cofix_subst mf mf' : fix_rel G mf mf' -> Forall2 G (cofix_subst mf) (cofix_subst mf').
  Proof.
    intros H. unfold cofix_subst. rewrite (Forall2_length H).
    induction #|mf'|; constructor; auto. apply G_s. now constructor.
  Qed.

  Lemma G_cunfold_fix mf mf' idx narg fn :
    fix_rel G mf mf' -> closedn 0 (tFix mf idx) -> closedn 0 (tFix mf' idx) ->
    cunfold_fix mf idx = Some (narg, fn) ->
    exists fn', cunfold_fix mf' idx = Some (narg, fn') /\ G fn fn'.
  Proof.
    intros H Hc Hc'. unfold cunfold_fix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-]. destruct (Forall2_nth_error_l _ _ _ _ _ H E) as (d' & -> & ? & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply G_substl; auto.
    - now apply G_fix_subst.
    - now apply closed_fix_subst.
    - now apply closed_fix_subst.
  Qed.

  Lemma G_cunfold_cofix mf mf' idx narg fn :
    fix_rel G mf mf' -> closedn 0 (tCoFix mf idx) -> closedn 0 (tCoFix mf' idx) ->
    cunfold_cofix mf idx = Some (narg, fn) ->
    exists fn', cunfold_cofix mf' idx = Some (narg, fn') /\ G fn fn'.
  Proof.
    intros H Hc Hc'. unfold cunfold_cofix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-]. destruct (Forall2_nth_error_l _ _ _ _ _ H E) as (d' & -> & ? & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply G_substl; auto.
    - now apply G_cofix_subst.
    - now apply closed_cofix_subst.
    - now apply closed_cofix_subst.
  Qed.

End Rel.

Lemma eval_construct_block_inv Σ ind c args w :
  eval Σ (tConstruct ind c args) w ->
  exists args', w = tConstruct ind c args' /\ ∥ All2_Set (eval Σ) args args' ∥.
Proof.
  intros ev. depelim ev.
  - eexists; split; [reflexivity|]. now sq.
  - destruct args; cbn in i; discriminate.
Qed.

Section Sim.
  Variables Σ Σ' : global_declarations.
  Hypothesis clΣ : closed_env Σ.
  Hypothesis clΣ' : closed_env Σ'.
  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall c decl b,
    declared_constant Σ c decl -> cst_body decl = Some b ->
    exists decl' b', declared_constant Σ' c decl' /\ cst_body decl' = Some b' /\ G Σ Σ' b b'.

  Notation G := (G Σ Σ').
  Notation Gs := (Gs Σ Σ').
  Notation Gv := (Gv Σ Σ').

  Definition simQ (v u : term) := exists v', ∥ eval Σ' u v' ∥ /\ Gv v v'.
  Definition sim_s (t v : term) := closedn 0 t -> forall u, Gs t u -> simQ v u.
  Definition sim_g (t v : term) := closedn 0 t -> forall u, G t u -> simQ v u.

  Lemma sim_lift t v : eval Σ t v -> sim_s t v -> sim_g t v.
  Proof.
    intros ev Hs Hc u H. revert ev Hs Hc.
    induction H as [t u H | fn decl' b' t Hd Hb Hcl H IH | va a' va' Hcl Hcl' [ev1] [ev2] Hv];
      intros ev Hs Hc.
    - now apply Hs.
    - destruct (IH ev Hs Hc) as (v' & [ev'] & Hv). exists v'. split; auto.
      sq. eapply eval_delta; tea.
    - have e := eval_deterministic ev ev1. subst v.
      exists va'. split; auto. now sq.
  Qed.

  Lemma Gv_head_shape v w : Gv v w ->
    [/\ isLambda v = isLambda w, isFix v = isFix w, isBox v = isBox w,
        isConstructApp v = isConstructApp w, isPrimApp v = isPrimApp w & isLazyApp v = isLazyApp w].
  Proof.
    unfold isConstructApp, isPrimApp, isLazyApp.
    induction 1; try (split; reflexivity).
    rewrite !head_tApp. destruct IHGv1. split; auto.
  Qed.

  Lemma Gv_mkApps_cofix mfix idx args w :
    Gv (mkApps (tCoFix mfix idx) args) w ->
    exists mfix' args', w = mkApps (tCoFix mfix' idx) args' /\ fix_rel G mfix mfix' /\ Forall2 Gv args args'.
  Proof.
    revert w; induction args as [|a args IH] using rev_ind; intros w H.
    - cbn in H. inversion H; subst. exists mf', []. cbn. auto.
    - rewrite mkApps_app in H. cbn in H. inversion H; subst.
      match goal with H : Gv (mkApps _ _) _ |- _ => destruct (IH _ H) as (mf' & args' & -> & ? & ?) end.
      eexists mf', (args' ++ [_]). rewrite mkApps_app. split; [reflexivity|split; auto].
      apply Forall2_app; auto.
  Qed.

  Lemma sim_args args args' (a : All2_Set (eval Σ) args args') :
    All2_over a (fun x y _ => sim_s x y) -> forallb (closedn 0) args ->
    forall args0, Forall2 G args args0 ->
    exists args1, ∥ All2_Set (eval Σ') args0 args1 ∥ /\ Forall2 Gv args' args1.
  Proof.
    induction a; cbn; intros iha Hc args0 H.
    - inversion H; subst. exists []. split; [sq; constructor | constructor].
    - destruct iha as [hx hl]. move/andP: Hc => [Hc1 Hc2]. inversion H; subst.
      match goal with ev : eval Σ ?x ?y, HG : G ?x _ |- _ =>
        destruct (sim_lift _ _ ev hx Hc1 _ HG) as (y' & [evy] & Hy) end.
      match goal with HG : Forall2 G _ _ |- _ =>
        destruct (IHa hl Hc2 _ HG) as (lr & [evl] & Hl) end.
      exists (y' :: lr). split; [sq; now constructor | now constructor].
  Qed.

  Lemma Gcl t u : closedn 0 t -> G t u -> closedn 0 u.
  Proof. apply G_closed. Qed.
  Lemma evcl t v : closedn 0 t -> eval Σ t v -> closedn 0 v.
  Proof. now apply eval_closed. Qed.
  Lemma evcl' t v : closedn 0 t -> eval Σ' t v -> closedn 0 v.
  Proof. now apply eval_closed. Qed.

  Lemma atom_eval_eq t w : atom Σ' t -> eval Σ' t w -> w = t.
  Proof. intros Ha ev. exact (eval_deterministic ev (eval_atom _ _ Ha)). Qed.

  Lemma All2_Set_diag (P : term -> term -> Set) l : All2_Set P l l -> Forall (fun x => ∥ P x x ∥) l.
  Proof.
    induction l; intros H; depelim H; constructor; auto. now sq.
  Qed.

  Lemma All2_Set_Forall2 (P : term -> term -> Set) l l' : All2_Set P l l' -> Forall2 (fun x y => ∥ P x y ∥) l l'.
  Proof. induction 1; constructor; auto. now sq. Qed.

  Lemma G_val_list args cargs args1 :
    Forall2 Gv args args1 -> Forall2 (fun x y => ∥ eval Σ' x y ∥) cargs args1 ->
    Forall (fun x => ∥ eval Σ x x ∥) args ->
    forallb (closedn 0) args -> forallb (closedn 0) cargs ->
    Forall2 G args cargs.
  Proof.
    intros H; revert cargs. induction H; intros cargs H2 Hv Hc Hc'; inversion H2; subst; constructor.
    - cbn in Hc, Hc'. rtoProp. inversion Hv; subst. eapply G_val; tea.
    - cbn in Hc, Hc'. rtoProp. inversion Hv; subst. eapply IHForall2; tea.
  Qed.

  Lemma value_args_diag ind c args v :
    eval Σ v (tConstruct ind c args) -> Forall (fun x => ∥ eval Σ x x ∥) args.
  Proof.
    intros ev. apply eval_to_value in ev. apply value_final in ev.
    apply eval_construct_block_inv in ev as (args' & [= <-] & [H]).
    now apply All2_Set_diag.
  Qed.

  Lemma mkApps_cofix_not_construct mfix idx args i c l :
    tConstruct i c l = mkApps (tCoFix mfix idx) args -> False.
  Proof.
    destruct args using rev_case; [discriminate|]. rewrite mkApps_app. discriminate.
  Qed.

  Ltac lft := repeat match goal with
    | ev : eval Σ ?t ?v, IH : sim_s ?t ?v, Hc : is_true (closedn 0 ?t), HG : ESpecRel.G Σ Σ' ?t ?u |- _ =>
      let w := fresh "w" in let evw := fresh "evw" in let Hw := fresh "Hw" in
      destruct (sim_lift _ _ ev IH Hc _ HG) as (w & [evw] & Hw); clear IH end.

  Lemma G_simulation_s t v (ev : eval Σ t v) : sim_s t v.
  Proof.
    induction ev using eval_rect; intros Hc u Hs.
    all: try (match goal with
              | H : context [with_guarded_fix] |- _ => cbv in H; discriminate H
              | H : context [with_constructor_as_block] |- _ => cbv in H; discriminate H
              | H : context [with_prop_case] |- _ => cbv in H; discriminate H end).
    all: cbn in Hc; rtoProp; inversion Hs; subst; lft.
    (* atoms *)
    all: try (match goal with i : is_true (atom _ (tConstruct _ _ ?args)) |- _ => destruct args; cbn in i; discriminate i end).
    all: try (match goal with i : is_true (atom _ _) |- _ => cbn in i; discriminate i end).
    all: try (match goal with i : is_true (atom _ _) |- _ =>
              eexists; split; [sq; eapply eval_atom; exact i | constructor; eassumption] end).
    (* box *)
    - inversion Hw0; subst. exists tBox. split; [|constructor]. sq. eapply eval_box; tea.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0.
    (* beta *)
    - match goal with HGf : G f0 ?f', HGa : G a ?a0 |- _ =>
        have Hcf' := Gcl _ _ H HGf; have Hca0 := Gcl _ _ H0 HGa end.
      have Hcl := evcl _ _ H ev1. have Hca' := evcl _ _ H0 ev2.
      have Hcw := evcl' _ _ Hca0 evw. have Hcw0 := evcl' _ _ Hcf' evw0.
      inversion Hw0; subst.
      match goal with HGb : G b ?b' |- _ =>
        have HG3 : G (csubst a' 0 b) (csubst w 0 b') by (apply G_csubst; auto using Gv_G) end.
      have Hc3 : closedn 0 (csubst a' 0 b) by now apply closed_csubst.
      lft. eexists. split; [|eassumption]. sq. eapply eval_beta; tea.
    - match goal with HGf : G f0 ?f', HGa : G a ?a0 |- _ =>
        have Hcf' := Gcl _ _ H HGf; have Hca0 := Gcl _ _ H0 HGa end.
      have Hcl := evcl _ _ H ev1. have Hca' := evcl _ _ H0 ev2.
      apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0; subst.
      match goal with HGb : G b ?b' |- _ =>
        have HG3 : G (csubst a' 0 b) (subst0 [a'0] b') end.
      { rewrite closed_subst //. apply G_subst0; cbn; rewrite ?Hca' ?Hca0 //.
        constructor; [|constructor]. eapply (G_val _ _ a' a'0 w); auto; [sq; apply value_final; eapply eval_to_value; tea | now sq]. }
      have Hc3 : closedn 0 (csubst a' 0 b) by now apply closed_csubst.
      lft. eexists. split; [|eassumption]. now sq.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0.
    (* zeta *)
    - match goal with HG0 : G b0 ?v' |- _ => have Hcv' := Gcl _ _ H HG0 end.
      have Hcb0' := evcl _ _ H ev1. have Hcw := evcl' _ _ Hcv' evw.
      match goal with HG1 : G b1 ?b' |- _ =>
        have HG3 : G (csubst b0' 0 b1) (csubst w 0 b') by (apply G_csubst; auto using Gv_G) end.
      have Hc3 : closedn 0 (csubst b0' 0 b1) by now apply closed_csubst.
      lft. eexists; split; [|eassumption]. sq. eapply eval_zeta; tea.
    (* iota *)
    - inversion Hw; subst.
      match goal with HG0 : G discr ?d' |- _ => have Hcd' := Gcl _ _ H HG0 end.
      have Hca := evcl _ _ H ev1. have Hca' := evcl' _ _ Hcd' evw. cbn in Hca, Hca'.
      match goal with Hb : brs_rel G brs _ |- _ =>
        destruct (Forall2_nth_error_l _ _ _ _ _ Hb e2) as (br' & e2' & Hb1 & Hb2) end.
      have HG3 : G (iota_red pars args br) (iota_red pars args' br').
      { unfold iota_red. apply G_substl; auto.
        - apply Forall2_List_rev, Forall2_skipn. now apply Forall2_Gv_G.
        - now rewrite forallb_rev forallb_skipn.
        - now rewrite forallb_rev forallb_skipn. }
      have Hc3 : closedn 0 (iota_red pars args br).
      { unfold iota_red. apply closed_substl; [now rewrite forallb_rev forallb_skipn|].
        rewrite List.length_rev e4. eapply (forallb_nth_error _ _ c) in H0. rewrite e2 in H0. exact H0. }
      lft. eexists; split; [|eassumption]. sq.
      match goal with Ha : Forall2 Gv args args' |- _ => have Hlen := Forall2_length Ha end.
      eapply eval_iota_block; tea.
      + rewrite -(same_constructor_isprop_pars_decl _ _ Hind). eassumption.
      + now rewrite -Hlen.
      + rewrite -Hb1 -e4 !length_skipn Hlen //.
    - apply eval_construct_block_inv in evw as (args1 & -> & [Hargs1]).
      inversion Hw; subst.
      match goal with HG0 : G discr ?d' |- _ => have Hcd' := Gcl _ _ H HG0 end.
      have Hca := evcl _ _ H ev1. cbn in Hca, Hcd'.
      match goal with Hb : brs_rel G brs _ |- _ =>
        destruct (Forall2_nth_error_l _ _ _ _ _ Hb e2) as (br'' & e2' & Hb1 & Hb2) end.
      match goal with Hn : nth_error brs' _ = Some br' |- _ => rewrite Hn in e2'; injection e2' as <- end.
      have HG3 : G (iota_red pars args br) (subst0 (List.rev (skipn pars cargs')) br'.2).
      { unfold iota_red. rewrite substl_subst; [now rewrite forallb_rev forallb_skipn|].
        apply G_subst0; auto.
        - apply Forall2_List_rev, Forall2_skipn. eapply G_val_list; tea.
          + now apply All2_Set_Forall2.
          + eapply value_args_diag; tea.
        - now rewrite forallb_rev forallb_skipn.
        - now rewrite forallb_rev forallb_skipn. }
      have Hc3 : closedn 0 (iota_red pars args br).
      { unfold iota_red. apply closed_substl; [now rewrite forallb_rev forallb_skipn|].
        rewrite List.length_rev e4. eapply forallb_nth_error in H0. erewrite e2 in H0. exact H0. }
      lft. eexists; split; [|eassumption]. now sq.
    (* fix *)
    - inversion Hw0; subst.
      match goal with HG0 : G f7 ?f' |- _ => have Hcf' := Gcl _ _ H HG0 end.
      match goal with HG0 : G a ?a' |- _ => have Hca0 := Gcl _ _ H0 HG0 end.
      have Hcfx := evcl _ _ H ev1. have Hcfx' := evcl' _ _ Hcf' evw0.
      have Hcav := evcl _ _ H0 ev2.
      match goal with Hf : fix_rel G mfix _ |- _ =>
        destruct (G_cunfold_fix _ _ _ _ _ _ _ Hf Hcfx Hcfx' e0) as (fn' & e0' & Hfn) end.
      have HG3 : G (tApp fn av) (tApp fn' w) by (apply G_s; constructor; auto using Gv_G).
      have Hc3 : closedn 0 (tApp fn av) by (cbn; rewrite Hcav (closed_cunfold_fix _ _ _ _ Hcfx e0) //).
      lft. eexists; split; [|eassumption]. sq. eapply eval_fix'; tea.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0; subst.
      match goal with HG0 : G a ?a' |- _ => have Hca0 := Gcl _ _ H0 HG0 end.
      have Hcfx := evcl _ _ H ev1. have Hcav := evcl _ _ H0 ev2.
      match goal with Hf : fix_rel G mfix _, Hcfx' : is_true (closed (tFix mfix' _)) |- _ =>
        destruct (G_cunfold_fix _ _ _ _ _ _ _ Hf Hcfx Hcfx' e0) as (fn'' & e0' & Hfn) end.
      match goal with Hn : cunfold_fix mfix' _ = Some (n, fn') |- _ => rewrite Hn in e0'; injection e0' as -> <- end.
      have HG3 : G (tApp fn av) (tApp fn' a').
      { apply G_s; constructor; auto. eapply (G_val _ _ av a' w); auto; [sq; apply value_final; eapply eval_to_value; tea | now sq]. }
      have Hc3 : closedn 0 (tApp fn av) by (cbn; rewrite Hcav (closed_cunfold_fix _ _ _ _ Hcfx e0) //).
      lft. eexists; split; [|eassumption]. now sq.
    (* cofix case *)
    - rename H into HCD.
      destruct (Gv_mkApps_cofix _ _ _ _ Hw) as (mfix' & args' & -> & Hmf & Hargs).
      match goal with HG0 : G discr ?d' |- _ => have Hcd' := Gcl _ _ HCD HG0 end.
      have Hcv := evcl _ _ HCD ev1. have Hcv' := evcl' _ _ Hcd' evw.
      rewrite closedn_mkApps in Hcv. rewrite closedn_mkApps in Hcv'.
      move/andP: Hcv => [Hcf Hcargs]. move/andP: Hcv' => [Hcf' Hcargs'].
      destruct (G_cunfold_cofix _ _ _ _ _ _ _ Hmf Hcf Hcf' e0) as (fn' & e0' & Hfn).
      have Hcfn := closed_cunfold_cofix _ _ _ _ Hcf e0.
      have HG3 : G (tCase ip (mkApps fn args) brs) (tCase ip (mkApps fn' args') brs').
      { apply G_s; constructor; auto. apply G_mkApps; auto using Forall2_Gv_G. }
      have Hc3 : closedn 0 (tCase ip (mkApps fn args) brs).
      { cbn. rewrite closedn_mkApps Hcfn Hcargs H0 //. }
      lft. eexists; split; [|eassumption]. sq. eapply eval_cofix_case; tea.
    - apply eval_construct_block_inv in evw as (args1 & -> & _).
      destruct (Gv_mkApps_cofix _ _ _ _ Hw) as (mfix' & args' & E & _).
      now apply mkApps_cofix_not_construct in E.
    (* cofix proj *)
    - rename Hc into HCD.
      destruct (Gv_mkApps_cofix _ _ _ _ Hw) as (mfix' & args' & -> & Hmf & Hargs).
      match goal with HG0 : G discr ?d' |- _ => have Hcd' := Gcl _ _ HCD HG0 end.
      have Hcv := evcl _ _ HCD ev1. have Hcv' := evcl' _ _ Hcd' evw.
      rewrite closedn_mkApps in Hcv. rewrite closedn_mkApps in Hcv'.
      move/andP: Hcv => [Hcf Hcargs]. move/andP: Hcv' => [Hcf' Hcargs'].
      destruct (G_cunfold_cofix _ _ _ _ _ _ _ Hmf Hcf Hcf' e0) as (fn' & e0' & Hfn).
      have Hcfn := closed_cunfold_cofix _ _ _ _ Hcf e0.
      have HG3 : G (tProj p (mkApps fn args)) (tProj p (mkApps fn' args')).
      { apply G_s; constructor; auto. apply G_mkApps; auto using Forall2_Gv_G. }
      have Hc3 : closedn 0 (tProj p (mkApps fn args)).
      { cbn. rewrite closedn_mkApps Hcfn Hcargs //. }
      lft. eexists; split; [|eassumption]. sq. eapply eval_cofix_proj; tea.
    (* delta *)
    - destruct (Hcst _ _ _ isdecl e) as (decl' & b' & Hd' & Hb' & HG).
      have Hcb := lookup_env_closed clΣ isdecl. cbn in Hcb. rewrite e in Hcb. cbn in Hcb.
      lft. eexists; split; [|eassumption]. sq. eapply eval_delta; tea.
    - unfold declared_constant in *.
      match goal with Hd : lookup_env Σ c = Some (ConstantDecl decl0) |- _ =>
        rewrite isdecl in Hd; injection Hd as <- end.
      match goal with Hb : cst_body decl = Some b |- _ => rewrite e in Hb; injection Hb as <- end.
      have Hcb := lookup_env_closed clΣ isdecl. cbn in Hcb. rewrite e in Hcb. cbn in Hcb.
      lft. eexists; split; [|eassumption]. now sq.
    (* proj block *)
    - inversion Hw; subst.
      match goal with Ha : Forall2 Gv args ?args' |- _ =>
        have Hlen := Forall2_length Ha;
        destruct (Forall2_nth_error_l _ _ _ _ _ Ha e3) as (a' & e3' & Ha') end.
      have Hca := evcl _ _ Hc ev1. cbn in Hca.
      eapply forallb_nth_error in Hca. erewrite e3 in Hca. cbn in Hca.
      apply Gv_G in Ha'.
      lft. eexists; split; [|eassumption]. sq. eapply eval_proj_block; tea.
      + rewrite -(same_constructor_isprop_pars_decl _ _ Hind). eassumption.
      + now rewrite -Hlen.
    (* construct block *)
    - match goal with Ha : Forall2 G args _ |- _ =>
        have Hlen := Forall2_length Ha;
        destruct (sim_args _ _ a iha Hc _ Ha) as (args1 & [evs] & Hargs1) end.
      eexists. split; [|constructor; eassumption].
      sq. eapply eval_construct_block; tea.
      + rewrite -(same_lookup_constructor _ _ Hind). eassumption.
      + now rewrite -Hlen.
    (* app cong *)
    - destruct (Gv_head_shape _ _ Hw0) as [E1 E2 E3 E4 E5 E6].
      eexists. split; [|constructor; eassumption].
      sq. eapply eval_app_cong; tea. cbn in i |- *.
      rewrite -E1 -E2 -E3 -E4 -E5 -E6. exact i.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0; subst. cbn in i. discriminate.
    - apply atom_eval_eq in evw0; [|reflexivity]. subst. inversion Hw0; subst. cbn in i. discriminate.
    (* prim *)
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - depelim X. cbn in Hc. move/andP: Hc => [Hcd Hcv].
      match goal with ev : All2_Set _ ?v _, a : All2_over ?ev _, H : Forall2 _ ?v _ |- _ =>
        destruct (sim_args _ _ ev a Hcv _ H) as (v1 & [evs] & Hv1) end.
      lft.
      eexists (tPrim (prim_array {| array_default := _; array_value := v1 |})).
      split; [sq; eapply eval_prim; now constructor|now constructor].
    (* force *)
    - inversion Hw; subst.
      have Hct' := evcl _ _ Hc ev1. cbn in Hct'.
      lft. eexists; split; [|eassumption]. sq. eapply eval_force; tea.
  Qed.
End Sim.

(** ** Whole-program stages and chains *)

Lemma G_simulation Σ Σ' :
  closed_env Σ -> closed_env Σ' ->
  (forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn) ->
  (forall c decl b, declared_constant Σ c decl -> cst_body decl = Some b ->
     exists decl' b', declared_constant Σ' c decl' /\ cst_body decl' = Some b' /\ G Σ Σ' b b') ->
  forall t u v, closedn 0 t -> G Σ Σ' t u -> eval Σ t v ->
  exists v', ∥ eval Σ' u v' ∥ /\ Gv Σ Σ' v v'.
Proof.
  intros cl cl' Hind Hcst t u v Hc HG ev.
  eapply (sim_lift Σ Σ' t v ev); eauto.
  eapply G_simulation_s; eauto.
Qed.

Definition gstage (p p' : program) : Prop :=
  [/\ closed_env p.1, closed_env p'.1,
      (forall kn, lookup_minductive p.1 kn = lookup_minductive p'.1 kn),
      (forall c decl b, declared_constant p.1 c decl -> cst_body decl = Some b ->
         exists decl' b', declared_constant p'.1 c decl' /\ cst_body decl' = Some b' /\ G p.1 p'.1 b b'),
      closedn 0 p.2 & G p.1 p'.1 p.2 p'.2].

Inductive gstages : program -> program -> Prop :=
| gstages_refl p : gstages p p
| gstages_step p p' p'' : gstage p p' -> gstages p' p'' -> gstages p p''.

Lemma gstages_trans p p' p'' : gstages p p' -> gstages p' p'' -> gstages p p''.
Proof. induction 1; auto. intros. econstructor; eauto. Qed.

Lemma gstages_one p p' : gstage p p' -> gstages p p'.
Proof. intros. econstructor; eauto. constructor. Qed.

(** The relation between the values of the two ends of a chain of stages:
    a chain of [Gv] steps, one per stage. *)
Inductive gchain : program -> program -> term -> term -> Prop :=
| gchain_refl p v : gchain p p v v
| gchain_step p p' p'' v v' v'' :
    gstage p p' -> Gv p.1 p'.1 v v' -> gchain p' p'' v' v'' -> gchain p p'' v v''.

Theorem gstages_eval p p' : gstages p p' ->
  forall v, ∥ eval p.1 p.2 v ∥ -> exists v', ∥ eval p'.1 p'.2 v' ∥ /\ gchain p p' v v'.
Proof.
  induction 1 as [p | p p' p'' Hst Hsts IH]; intros v [ev].
  - exists v. split; [now sq | constructor].
  - destruct Hst as [cl cl' Hind Hcst Hc HG].
    destruct (G_simulation _ _ cl cl' Hind Hcst _ _ _ Hc HG ev) as (v' & ev' & Hv).
    destruct (IH _ ev') as (v'' & ev'' & Hch).
    exists v''. split; auto. econstructor; eauto. split; auto.
Qed.

(** *** Changing the body of one constant *)

Lemma lookup_env_mid pre kn d d' lo c x :
  lookup_env (pre ++ (kn, d) :: lo) c = Some x ->
  lookup_env (pre ++ (kn, d') :: lo) c = Some x \/
  (x = d /\ lookup_env (pre ++ (kn, d') :: lo) c = Some d').
Proof.
  induction pre as [|[kn' d0] pre IH]; cbn.
  - destruct (eqb_spec c kn); [intros [= <-]; right; auto | intros; left; auto].
  - destruct (eqb_spec c kn'); [intros; left; auto | auto].
Qed.

Lemma closed_env_app Σ1 Σ2 : closed_env (Σ1 ++ Σ2) = closed_env Σ1 && closed_env Σ2.
Proof. unfold closed_env. now rewrite forallb_app. Qed.

Lemma gstage_one pre lo kn B B' t :
  let Σa := pre ++ (kn, ConstantDecl {| cst_body := Some B |}) :: lo in
  let Σb := pre ++ (kn, ConstantDecl {| cst_body := Some B' |}) :: lo in
  closed_env Σa -> closedn 0 t -> G Σa Σb B B' -> gstage (Σa, t) (Σb, t).
Proof.
  intros Σa Σb cl Hc HG.
  have clB : closedn 0 B.
  { subst Σa. rewrite closed_env_app in cl. move/andP: cl => [_ cl]. cbn in cl. now move/andP: cl => [cl _]. }
  have clB' := G_closed _ _ _ _ _ clB HG.
  split; cbn [fst snd]; auto.
  - subst Σa Σb. rewrite closed_env_app in cl. rewrite closed_env_app.
    move/andP: cl => [cl1 cl2]. rewrite cl1. cbn in cl2 |- *.
    move/andP: cl2 => [_ cl2]. now rewrite clB' cl2.
  - intros c. unfold lookup_minductive. subst Σa Σb.
    destruct (lookup_env (pre ++ (kn, ConstantDecl {| cst_body := Some B |}) :: lo) c) eqn:E.
    + destruct (lookup_env_mid _ _ _ (ConstantDecl {| cst_body := Some B' |}) _ _ _ E) as [-> | [-> ->]]; reflexivity.
    + destruct (lookup_env (pre ++ (kn, ConstantDecl {| cst_body := Some B' |}) :: lo) c) eqn:E'; auto.
      destruct (lookup_env_mid _ _ _ (ConstantDecl {| cst_body := Some B |}) _ _ _ E') as [E2 | [-> E2]];
        rewrite E in E2; discriminate.
  - intros c decl b Hd Hb. unfold declared_constant in *.
    destruct (lookup_env_mid _ _ _ (ConstantDecl {| cst_body := Some B' |}) _ _ _ Hd) as [E | [[= ->] E]].
    + exists decl, b. repeat split; auto. apply G_refl.
    + cbn in Hb. injection Hb as <-. eexists _, B'. repeat split; eauto.
  - apply G_refl.
Qed.
