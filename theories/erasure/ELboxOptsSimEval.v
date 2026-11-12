(** * Forward simulation for the rewrite relation of [ELboxOptsSim]

    If [t] evaluates to [v] in [Σ] and [R Σ' t t'], then [t'] evaluates in
    [Σ'] to some [v'] with [R Σ' v v'].  The flags are those of the pipeline
    stage where the lambda-box passes run: constructors as blocks, unguarded
    fixpoints, no propositional cases. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv EWcbvEval EProgram EWellformed.
From Peregrine Require Import ELboxOpts ELboxOptsSim.
From Peregrine Require ELiftConstants.
From Equations Require Import Equations.

Local Open Scope bool_scope.
Set Default Goal Selector "!".

Section Sim.
  Context {wfl : WcbvFlags}.
  Hypothesis Hblock : with_constructor_as_block = true.
  Hypothesis Hguard : with_guarded_fix = false.
  Hypothesis Hprop : with_prop_case = false.
  Variables Σ Σ' : global_declarations.

  Lemma Rs_app l l' m m' : Rs Σ' l l' -> Rs Σ' m m' -> Rs Σ' (l ++ m) (l' ++ m').
  Proof. rewrite !Rs_Forall2. apply Forall2_app. Qed.

  (** A value on the right is related by a head rule, unless it is an
      unevaluated cofixpoint standing for a constructor. *)
  Lemma R_value t w :
    R Σ' t w -> ∥ value Σ' w ∥ -> Rh Σ' t w \/ exists ind c args, t = tConstruct ind c args.
  Proof.
    induction 1; intros [vw].
    - now left.
    - right. eauto.
    - match goal with H : ∥ eval _ _ _ ∥ |- _ => destruct H as [e] end.
      have E := eval_value _ _ vw e. subst. apply IHR. now sq.
  Qed.

  Ltac rvalue H v H' :=
    destruct (R_value _ _ H v) as [H'|(?&?&?&?)]; [|discriminate].

  Lemma R_box_inv w : R Σ' tBox w -> ∥ value Σ' w ∥ -> w = tBox.
  Proof. intros H v. rvalue H v H'. now inversion H'. Qed.

  Lemma R_lambda_inv na b w :
    R Σ' (tLambda na b) w -> ∥ value Σ' w ∥ -> exists b', w = tLambda na b' /\ R Σ' b b'.
  Proof. intros H v. rvalue H v H'. inversion H'; subst; eauto. Qed.

  Lemma R_fix_inv mf idx w :
    R Σ' (tFix mf idx) w -> ∥ value Σ' w ∥ -> exists mf', w = tFix mf' idx /\ Rdefs Σ' mf mf'.
  Proof. intros H v. rvalue H v H'. inversion H'; subst; eauto. Qed.

  Lemma R_lazy_inv b w :
    R Σ' (tLazy b) w -> ∥ value Σ' w ∥ -> exists b', w = tLazy b' /\ R Σ' b b'.
  Proof. intros H v. rvalue H v H'. inversion H'; subst; eauto. Qed.

  Lemma R_mkApps_cofix_inv mf idx args w :
    R Σ' (mkApps (tCoFix mf idx) args) w -> ∥ value Σ' w ∥ ->
    exists mf' args', w = mkApps (tCoFix mf' idx) args' /\ Rdefs Σ' mf mf' /\ Rs Σ' args args'.
  Proof.
    revert w. induction args using rev_ind; intros w H v.
    - cbn in H. rvalue H v H'. inversion H'; subst.
      eexists _, []. cbn. repeat split; eauto. constructor.
    - rewrite mkApps_app in H. cbn in H. rvalue H v H'.
      have Hhd := mkApps_cofix_head mf idx args.
      inversion H'; subst.
      + destruct v as [v].
        match goal with H : R _ (mkApps _ args) _ |- _ =>
          destruct (IHargs _ H) as (mf' & args' & -> & ? & ?) end.
        { sq. eapply value_app_head; tea. }
        eexists mf', (args' ++ [_]). rewrite mkApps_app. cbn. repeat split; eauto.
        apply Rs_app; auto. constructor; auto. constructor.
      + match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
      + match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
      + match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
  Qed.

  Lemma R_construct_unfolds t w :
    R Σ' t w -> forall ind c args, t = tConstruct ind c args ->
    ∥ value Σ' w ∥ -> closed w ->
    exists args', unfolds Σ' w (tConstruct ind c args') /\ Rs Σ' args args' /\
      ∥ value Σ' (tConstruct ind c args') ∥ /\ closed (tConstruct ind c args').
  Proof.
    induction 1; intros ind0 c0 args0 E vw clw.
    - subst. match goal with H : Rh _ _ _ |- _ => inversion H; subst end.
      eexists; split; [constructor|]. auto.
    - injection E; intros; subst.
      destruct (IHR _ _ _ eq_refl) as (args'' & U & HR & vv & clv); auto.
      { match goal with H : ∥ eval _ _ v0 ∥ |- _ => destruct H as [e] end.
        sq. eapply eval_to_value; tea. }
      exists args''. split; [eapply unfolds_step; tea|auto].
    - destruct vw as [vw].
      match goal with H : ∥ eval _ _ _ ∥ |- _ => destruct H as [e] end.
      have E' := eval_value _ _ vw e. subst. apply IHR; auto. now sq.
  Qed.

  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall kn b, declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σ' kn {| cst_body := Some b' |} /\ R Σ' b b'.
  Hypothesis HclΣ : closed_env Σ.
  Hypothesis HclΣ' : closed_env Σ'.
  Hypothesis Hpars : forall ind c b pars cdecl,
    constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.

  Lemma value_cofix_shape f :
    value Σ f ->
    ~~ (isLambda f || (if with_guarded_fix then isFixApp f else isFix f) || isBox f
        || isConstructApp f || isPrimApp f || isLazyApp f) ->
    exists mfix idx args, f = mkApps (tCoFix mfix idx) args.
  Proof.
    rewrite Hguard. intros [t X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
    - destruct X as [t i|p ?].
      + destruct t; cbn in i |- *; try discriminate.
        all: try (intros; discriminate).
        intros _. now eexists _, _, [].
      + cbn. intros; discriminate.
    - cbn. rewrite ?orb_true_r. intros; discriminate.
    - destruct vh.
      + congruence.
      + intros _. now eexists _, _, _.
      + rewrite Hguard in y. destruct y.
  Qed.

  Definition goal t' v := exists v', ∥ eval Σ' t' v' ∥ /\ R Σ' v v'.

  Lemma sim_layer t v :
    eval Σ t v -> (forall t', Rh Σ' t t' -> goal t' v) -> forall t', R Σ' t t' -> goal t' v.
  Proof.
    intros ev Hh t' H. revert v ev Hh. induction H; intros v ev Hh.
    - now apply Hh.
    - destruct (IHR v ev Hh) as (v0' & [e0] & Hv).
      match goal with H : ∥ eval _ _ v0 ∥ |- _ => destruct H as [e1] end.
      have vv0 := eval_to_value _ _ e1.
      have E : v0 = v0' by (eapply eval_value; tea). subst v0'.
      eexists. split.
      { match goal with H : ∥ value _ _ ∥ |- _ => destruct H as [vv] end.
        sq. now apply value_final. }
      eapply eval_Construct_inv in ev as (args'' & -> & _).
      eapply R_cofix; tea. now sq.
    - destruct (IHR v ev Hh) as (v0' & [e0] & Hv).
      match goal with H : ∥ eval _ _ v0 ∥ |- _ => destruct H as [e1] end.
      have E : v0 = v0' by (eapply eval_value; [eapply eval_to_value; exact e1|exact e0]).
      subst v0'. exists v0. split; [now sq|auto].
  Qed.

  Lemma sim_args args args' (a : All2_Set (eval Σ) args args') :
    All2_over a (fun x y _ => closed x -> forall t', Rh Σ' x t' -> goal t' y) ->
    forallb (closedn 0) args ->
    forall args0, Rs Σ' args args0 ->
    exists args1, ∥ All2_Set (eval Σ') args0 args1 ∥ /\ Rs Σ' args' args1.
  Proof.
    induction a; cbn; intros iha cl args0 Hargs; inversion Hargs; subst.
    - exists []. split; [sq; constructor|constructor].
    - destruct iha as [hx hl]. move/andP: cl => [cx cl].
      match goal with H : R _ x _ |- _ =>
        destruct (sim_layer _ _ r (hx cx) _ H) as (y' & [ey] & Hy) end.
      match goal with H : Rs _ l _ |- _ =>
        destruct (IHa hl cl _ H) as (l1 & [el] & Hl) end.
      exists (y' :: l1). split; [sq; now constructor|now constructor].
  Qed.

  Lemma closed_iota_red ip d pars args br brs c :
    closed (tCase ip d brs) -> forallb (closedn 0) args ->
    nth_error brs c = Some br -> #|skipn pars args| = #|br.1| ->
    closed (iota_red pars args br).
  Proof.
    cbn. move/andP => [_ Hc'] cla e2 e4. rewrite /iota_red.
    eapply closed_substl. { now rewrite forallb_rev forallb_skipn. }
    len. rewrite e4. eapply nth_error_forallb in Hc'; tea.
    now rewrite Nat.add_0_r in Hc'.
  Qed.

  Ltac sim_with_n t t' w e Hw :=
    match goal with
    | IH : is_true (closedn 0 t) -> forall t', Rh _ t t' -> goal t' ?v, ev : eval _ t ?v |- _ =>
      let c := fresh "c" in
      assert (c : closed t);
      [| destruct (sim_layer _ _ ev (IH c) t') as (w & [e] & Hw); [|clear IH]]
    end.
  Ltac sim_ev ev w e Hw :=
    match type of ev with eval _ ?t _ =>
      match goal with HR : R _ t ?t' |- _ => sim_with_n t t' w e Hw; [ | exact HR | ] end end.
  Ltac sim_ev_with ev t' w e Hw :=
    match type of ev with eval _ ?t _ => sim_with_n t t' w e Hw end.
  Ltac ind_tac :=
    first [ now rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind)
          | now rewrite -(ELiftConstants.same_inductive_isprop_and_pars _ _ Hind)
          | now rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind) ].
  Ltac split_cl cl c1 c2 := cbn in cl; move/andP: cl => [c1 c2].
  Ltac tgt_closed Ht cl cl0 :=
    have cl0 := R_closed _ _ _ 0 (R_head _ _ _ Ht) cl.

  (** The rules for applications: all of them reduce to the congruence
      rule, except for the contraction of a source beta redex. *)
  Lemma app_head f a res t0 :
    closed (tApp f a) ->
    (forall f' a', R Σ' f f' -> R Σ' a a' -> closed f' -> closed a' ->
      goal (tApp f' a') res) ->
    (forall na b b' a', f = tLambda na b -> R Σ' b b' -> R Σ' a a' ->
      closedn 1 b' -> closed a' -> goal (csubst a' 0 b') res) ->
    Rh Σ' (tApp f a) t0 -> goal t0 res.
  Proof.
    intros cl Hc Hb Ht. split_cl cl c1 c2. inversion Ht; subst.
    - apply Hc; auto; eapply R_closed; tea.
    - have ca' := R_closed _ _ _ 0 ltac:(eassumption) c2.
      cbn in c1.
      match goal with H : R _ b _ |- _ => have cb' := R_closed _ _ _ 1 H c1 end.
      unfold subst1. rewrite -closed_subst //.
      eapply Hb; eauto.
    - have ca' := R_closed _ _ _ 0 ltac:(eassumption) c2.
      edestruct (Hc (tLetIn z v' b')) as (w & [e] & Hw).
      + apply R_head; constructor; eassumption.
      + eassumption.
      + eapply R_closed; [|exact c1]. apply R_head; constructor; eassumption.
      + exact ca'.
      + exists w. split; [|exact Hw]. sq. eapply eval_app_let; tea.
    - have ca' := R_closed _ _ _ 0 ltac:(eassumption) c2.
      edestruct (Hc (tCase ci d' brs')) as (w & [e] & Hw).
      + apply R_head; constructor; eassumption.
      + eassumption.
      + eapply R_closed; [|exact c1]. apply R_head; constructor; eassumption.
      + exact ca'.
      + exists w. split; [|exact Hw]. sq. eapply eval_app_case; tea.
  Qed.

  Ltac vof e := sq; eapply eval_to_value; exact e.

  Lemma simulation_head t v (ev : eval Σ t v) :
    closed t -> forall t', Rh Σ' t t' -> goal t' v.
  Proof.
    induction ev using eval_rect; intros cl t0 Ht.
    all: try (exfalso; unfold is_true in *; congruence).
    - (* box *)
      eapply app_head; [exact cl| | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. discriminate. }
      intros f' a' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      apply R_box_inv in Hw; [subst|vof ee0].
      exists tBox. split; [sq; eapply eval_box; tea|apply R_refl].
    - (* beta *)
      eapply app_head; [exact cl| | |exact Ht].
      2:{ intros na0 b0 b0' a0' -> Hb0 Ha0 cb0' ca0'. split_cl cl c1 c2.
          apply eval_lambda_inv in ev1. injection ev1 as <- <-.
          sim_ev ev2 w2 ee2 Hw2; [auto|].
          have cw2 := eval_closed Σ' HclΣ' _ _ ca0' ee2.
          have Ha2 : R Σ' a' a0' by (eapply R_eval; [exact Hw2|sq; exact ee2|auto|auto]).
          have ca' := eval_closed Σ HclΣ _ _ c2 ev2.
          sim_ev_with ev3 (csubst a0' 0 b0') w3 ee3 Hw3;
            [apply closed_csubst; auto | apply R_csubst; auto | ].
          exists w3. split; [now sq|auto]. }
      intros f' a0' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      apply R_lambda_inv in Hw as (b' & -> & Hb); [|vof ee0].
      have cw2 := eval_closed Σ' HclΣ' _ _ c2' ee2.
      have ca' := eval_closed Σ HclΣ _ _ c2 ev2.
      have clam := eval_closed Σ HclΣ _ _ c1 ev1. cbn in clam.
      sim_ev_with ev3 (csubst w2 0 b') w3 ee3 Hw3;
        [apply closed_csubst; auto | apply R_csubst; auto | ].
      exists w3. split; [sq; eapply eval_beta; tea|auto].
    - (* zeta *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      split_cl cl c1 c2. split_cl cl0 c1' c2'.
      sim_ev ev1 w ee0 Hw; [auto|].
      have cw := eval_closed Σ' HclΣ' _ _ c1' ee0.
      have cb0' := eval_closed Σ HclΣ _ _ c1 ev1.
      match type of ev2 with eval _ (csubst _ 0 ?b1) _ =>
        match goal with HR : R _ b1 ?b1' |- _ =>
        sim_ev_with ev2 (csubst w 0 b1') w3 ee3 Hw3;
        [apply closed_csubst; auto | apply R_csubst; auto | ] end end.
      exists w3. split; [sq; eapply eval_zeta; tea|auto].
    - (* iota block *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      + (* congruence *)
        have cl' := cl. split_cl cl c1 c2. split_cl cl0 c1' c2'.
        sim_ev ev1 w ee5 Hw; [auto|].
        have cw := eval_closed Σ' HclΣ' _ _ c1' ee5.
        have cargs := eval_closed Σ HclΣ _ _ c1 ev1. cbn in cargs.
        destruct (R_construct_unfolds _ _ Hw _ _ _ eq_refl) as (args' & U & Hargs & [vv] & clv);
          [sq; eapply eval_to_value; tea|auto|].
        cbn in clv.
        match goal with HR : Rbrs _ ?brs ?brs', Hn : nth_error ?brs _ = Some _ |- _ =>
          destruct (Rbrs_nth_error _ _ _ _ _ HR Hn) as (br' & Hn' & Hb1 & Hb2) end.
        match type of ev2 with eval _ (iota_red ?pars _ _) _ =>
          sim_ev_with ev2 (iota_red pars args' br') w3 ee6 Hw3;
          [eapply closed_iota_red; tea | apply R_iota_red; auto | ] end.
        exists w3. split; [|auto].
        match goal with |- ∥ eval _ (tCase ?ip _ ?brs') _ ∥ =>
          match type of U with unfolds _ _ ?k =>
            assert (ev' : eval Σ' (tCase ip k brs') w3) end end.
        { eapply eval_iota_block;
            [exact Hblock | apply value_final; exact vv
            | rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); eassumption
            | exact Hn' | rewrite -(Rs_length _ _ _ Hargs); eassumption
            | rewrite -Hb1 -(Rs_length _ _ _ (Rs_skipn _ _ _ _ Hargs)); eassumption
            | exact ee6]. }
        destruct (unfolds_case _ _ _ _ _ _ U ev') as [ev'']. sq.
        eapply eval_case_scrut; tea.
      + (* identity case *)
        split_cl cl c1 c2.
        sim_ev ev1 w ee5 Hw; [auto|].
        exists w. split; [now sq|].
        have cargs := eval_closed Σ HclΣ _ _ c1 ev1. cbn in cargs.
        match goal with H : constructor_isprop_pars_decl _ _ _ = Some (_, ?q, _) |- _ =>
          pose proof (Hpars _ _ _ _ _ H) as Hq; subst q end.
        match goal with H : #|skipn 0 _| = _ |- _ => rewrite skipn_0 in H end.
        match type of ev2 with eval _ _ ?r => match type of ev1 with eval _ _ ?k =>
          enough (E : r = k) by (rewrite E; exact Hw) end end.
        eapply case_id_iota; tea.
        * eapply all_rebuild_nth; tea.
        * eapply eval_to_value; tea.
    - (* fix' *)
      eapply app_head; [exact cl| | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. discriminate. }
      intros f' a0' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      apply R_fix_inv in Hw as (mf' & -> & Hmf); [|vof ee0].
      have cfx := eval_closed Σ' HclΣ' _ _ c1' ee0.
      have cfs := eval_closed Σ HclΣ _ _ c1 ev1.
      edestruct R_cunfold_fix as (fn' & Hfn' & HRfn); [exact Hmf|exact cfx|eassumption|].
      sim_ev_with ev3 (tApp fn' w2) w3 ee3 Hw3.
      { cbn. apply/andP; split; [eapply closed_cunfold_fix; [exact cfs|eassumption]|exact (eval_closed Σ HclΣ _ _ c2 ev2)]. }
      { apply R_head; constructor; auto. }
      exists w3. split; [sq; eapply eval_fix'; tea|auto].
    - (* cofix case *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      + split_cl cl c1 c2. split_cl cl0 c1' c2'.
        sim_ev ev1 w ee0 Hw; [auto|].
        apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
        have cw := eval_closed Σ' HclΣ' _ _ c1' ee0.
        rewrite closedn_mkApps in cw. move/andP: cw => [cw1 cw2].
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact cw1|eassumption|].
        match type of ev2 with eval _ (tCase _ ?d _) _ => assert (csrc : closed d) end.
        { have := eval_closed Σ HclΣ _ _ c1 ev1. rewrite !closedn_mkApps.
          move/andP => [x1 x2]. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
        match goal with HR : Rbrs _ _ ?brs' |- _ =>
          match type of ev2 with eval _ (tCase ?ip _ _) _ =>
          sim_ev_with ev2 (tCase ip (mkApps fn' args') brs') w3 ee3 Hw3 end end.
        { cbn. apply/andP; split; auto. }
        { apply R_head; constructor; auto. apply R_mkApps; auto. }
        exists w3. split; [sq; eapply eval_cofix_case; tea|auto].
      + split_cl cl c1 c2.
        sim_ev ev1 w ee0 Hw; [auto|].
        apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
        have cw := eval_closed Σ' HclΣ' _ _ cl0 ee0.
        have cw' := cw.
        rewrite closedn_mkApps in cw. move/andP: cw => [cw1 cw2].
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact cw1|eassumption|].
        match type of ev2 with eval _ (tCase _ ?d _) _ => assert (csrc : closed d) end.
        { have := eval_closed Σ HclΣ _ _ c1 ev1. rewrite !closedn_mkApps.
          move/andP => [x1 x2]. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
        sim_ev_with ev2 (mkApps fn' args') w3 ee3 Hw3.
        { cbn. apply/andP; split; auto. }
        { apply R_head; apply Rh_case_id; auto. apply R_mkApps; auto. }
        edestruct case_id_result as (cc & argsc & E); [..|exact ev2|reflexivity|exact csrc|eassumption|]; tea.
        rewrite E in Hw3 |- *.
        exists (mkApps (tCoFix mf' idx) args'). split; [now sq|].
        eapply R_cofix; tea.
        * now sq.
        * sq. eapply eval_to_value; tea.
        * eapply eval_closed; [exact HclΣ'| |exact ee3].
          rewrite closedn_mkApps. apply/andP; split; auto. eapply closed_cunfold_cofix; tea.
    - (* cofix proj *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      cbn in cl, cl0.
      sim_ev ev1 w ee0 Hw; [auto|].
      apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
      have cw := eval_closed Σ' HclΣ' _ _ cl0 ee0.
      rewrite closedn_mkApps in cw. move/andP: cw => [cw1 cw2].
      edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact cw1|eassumption|].
      match type of ev2 with eval _ (tProj ?p ?d) _ =>
        assert (csrc : closed d);
        [|sim_ev_with ev2 (tProj p (mkApps fn' args')) w3 ee3 Hw3] end.
      { have := eval_closed Σ HclΣ _ _ cl ev1. rewrite !closedn_mkApps.
        move/andP => [x1 x2]. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
      { exact csrc. }
      { apply R_head; constructor; auto. apply R_mkApps; auto. }
      exists w3. split; [sq; eapply eval_cofix_proj; tea|auto].
    - (* delta *)
      inversion Ht; subst.
      destruct decl as [body0]. cbn in e. subst body0.
      destruct (Hcst _ _ isdecl) as (b' & Hd & Hb).
      sim_ev_with ev b' w ee0 Hw.
      { move/(lookup_env_closed HclΣ): isdecl. now rewrite /closed_decl /=. }
      { exact Hb. }
      exists w. split; [sq; eapply eval_delta; tea; reflexivity|auto].
    - (* proj block *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      cbn in cl, cl0.
      sim_ev ev1 w ee0 Hw; [auto|].
      have cw := eval_closed Σ' HclΣ' _ _ cl0 ee0.
      have cargs := eval_closed Σ HclΣ _ _ cl ev1. cbn in cargs.
      destruct (R_construct_unfolds _ _ Hw _ _ _ eq_refl) as (args' & U & Hargs & [vv] & clv);
        [sq; eapply eval_to_value; tea|auto|].
      match goal with Hn : nth_error _ _ = Some _ |- _ =>
        destruct (Rs_nth_error _ _ _ _ _ Hargs Hn) as (a' & Hn' & Ha');
        have ca := nth_error_forallb Hn cargs end.
      sim_ev_with ev2 a' w3 ee3 Hw3; [exact ca|exact Ha'|].
      exists w3. split; [|auto].
      match goal with |- ∥ eval _ (tProj ?p _) _ ∥ =>
        match type of U with unfolds _ _ ?k =>
          assert (ev' : eval Σ' (tProj p k) w3) end end.
      { eapply eval_proj_block;
          [exact Hblock | apply value_final; exact vv
          | rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); eassumption
          | rewrite -(Rs_length _ _ _ Hargs); eassumption
          | exact Hn' | exact ee3]. }
      destruct (unfolds_proj _ _ _ _ _ U ev') as [ev'']. sq.
      eapply eval_proj_scrut; tea.
    - (* construct block *)
      inversion Ht; subst. cbn in cl.
      match goal with H : Rs _ args _ |- _ =>
        destruct (sim_args _ _ a iha cl _ H) as (args1 & [evs] & Hargs1);
        have Hlen := Rs_length _ _ _ H end.
      eexists. split; [|apply R_head; constructor; eassumption].
      sq. eapply eval_construct_block;
        [exact Hblock
        | rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind); eassumption
        | rewrite -Hlen; eassumption | exact evs].
    - (* app cong *)
      eapply app_head; [exact cl| | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. subst. discriminate. }
      intros f0' a0' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      destruct (value_cofix_shape _ (eval_to_value _ _ ev1) i) as (mfix & idx & args & E).
      rewrite E in Hw |- *.
      apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
      eexists. split; [sq; eapply eval_app_cong; tea|].
      + rewrite Hguard isConstructApp_mkApps isPrimApp_mkApps isLazyApp_mkApps.
        destruct args' using rev_case; rewrite ?mkApps_app; reflexivity.
      + apply R_head; constructor; auto. apply R_mkApps; auto. apply R_head; constructor; auto.
    - (* prim *)
      depelim X; inversion Ht; subst.
      1-3: eexists; split; [sq; eapply eval_prim; constructor|apply R_refl].
      cbn in cl. unfold test_array_model in cl. cbn in cl.
      move/andP: cl => [cd cv].
      match goal with H : Rs _ v _ |- _ =>
        destruct (sim_args _ _ ev a cv _ H) as (v1 & [evs] & Hv1) end.
      match goal with H : R _ def _ |- _ =>
        destruct (sim_layer _ _ ed (g cd) _ H) as (d1 & [evd] & Hd1) end.
      exists (tPrim (prim_array {| array_default := d1; array_value := v1 |})).
      split; [sq; eapply eval_prim; now constructor|apply R_head; now constructor].
    - (* force *)
      tgt_closed Ht cl cl0. inversion Ht; subst. cbn in cl, cl0.
      sim_ev ev1 w ee0 Hw; [auto|].
      apply R_lazy_inv in Hw as (b' & -> & Hb); [|vof ee0].
      have cv := eval_closed Σ HclΣ _ _ cl ev1. cbn in cv.
      sim_ev_with ev2 b' w3 ee3 Hw3; [exact cv|exact Hb|].
      exists w3. split; [sq; eapply eval_force; tea|auto].
    - (* atoms *)
      destruct t; cbn in i; try discriminate.
      all: try (rewrite Hblock in i; destruct args; discriminate).
      all: inversion Ht; subst.
      all: eexists; split; [sq; apply eval_atom; reflexivity|apply R_head; exact Ht].
  Qed.

  Theorem simulation t v t' :
    eval Σ t v -> closed t -> R Σ' t t' -> goal t' v.
  Proof.
    intros ev cl H. exact (sim_layer _ _ ev (simulation_head _ _ ev cl) _ H).
  Qed.

End Sim.
