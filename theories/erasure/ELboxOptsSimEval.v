(** * Forward simulation for the rewrite relation of [ELboxOptsSim]

    If [t] evaluates to [v] in [Σ] and [R Σ' t t'], then [t'] evaluates in
    [Σ'] to some [v'] with [R Σ' v v'].  The flags are any with unguarded
    fixpoints and no propositional cases; constructor applications are blocks
    or applications ([cval]), and the cases of a match and of a projection are
    proved once for both ([sim_iota], [sim_proj]). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv EWcbvEval EProgram EWellformed.
From Peregrine Require Import ELboxOpts ELboxOptsSimDB ELboxOptsSim.
From Peregrine Require ELiftConstants.
From Equations Require Import Equations.

Local Open Scope bool_scope.
Set Default Goal Selector "!".

Section Sim.
  Context {wfl : WcbvFlags}.
  Hypothesis Hguard : with_guarded_fix = false.
  Hypothesis Hprop : with_prop_case = false.
  Variables Σ Σ' : global_declarations.

  Lemma Rs_app l l' m m' : Rs Σ' l l' -> Rs Σ' m m' -> Rs Σ' (l ++ m) (l' ++ m').
  Proof. rewrite !Rs_Forall2. apply Forall2_app. Qed.

  Lemma R_mk_lambdas xs ys e e' :
    #|xs| = #|ys| -> R Σ' e e' -> R Σ' (mk_lambdas xs e) (mk_lambdas ys e').
  Proof.
    revert ys; induction xs; destruct ys; cbn; intros; try discriminate; auto.
    apply R_head; constructor. apply IHxs; auto; lia.
  Qed.

  Lemma R_substl_at k s s' t t' :
    Rs Σ' s s' -> forallb (closedn 0) s -> forallb (closedn 0) s' -> R Σ' t t' ->
    R Σ' (substl_at k s t) (substl_at k s' t').
  Proof.
    intros H; revert t t'; induction H; cbn; intros t0 t0' cl0 cl Ht; auto.
    move/andP: cl0 => [d1 d2]. move/andP: cl => [c1 c2]. apply IHRs; auto. apply R_csubst; auto.
  Qed.

  (** *** Arity of the target of [fix_eta] *)

  Lemma has_lambdas_S_inv m w :
    has_lambdas (S m) w -> exists na b, w = tLambda na b /\ has_lambdas m b.
  Proof. destruct w; cbn; try discriminate; eauto. Qed.

  Lemma has_lambdas_substl s m t : has_lambdas m t -> has_lambdas m (substl s t).
  Proof.
    unfold substl. induction s in t |- *; cbn; auto.
    intros H. now apply IHs, has_lambdas_csubst.
  Qed.

  Lemma tarity_lam m : forall w, has_lambdas (S m) w -> tarity Σ' m w.
  Proof.
    induction m; intros w H; cbn [tarity]; auto. intros a' ca' [va'].
    destruct (has_lambdas_S_inv _ _ H) as (na & b & -> & Hb).
    have Hb' := has_lambdas_csubst a' 0 _ _ Hb.
    destruct (has_lambdas_S_inv _ _ Hb') as (na' & b' & E & _).
    exists (csubst a' 0 b). split; [|now apply IHm].
    sq. eapply eval_beta; [apply eval_atom; reflexivity|now apply value_final|].
    rewrite E. apply eval_atom. reflexivity.
  Qed.

  Lemma tarity_fix m mf idx : fix_arity_ok mf idx (S m) -> tarity Σ' m (tFix mf idx).
  Proof.
    unfold fix_arity_ok. destruct (nth_error mf idx) as [d|] eqn:E; [|discriminate]. intros H.
    destruct m; cbn [tarity]; auto. intros a' ca' [va'].
    have Hs := has_lambdas_substl (fix_subst mf) _ _ H.
    destruct (has_lambdas_S_inv _ _ Hs) as (na & b & Eb & Hb).
    have Hb' := has_lambdas_csubst a' 0 _ _ Hb.
    destruct (has_lambdas_S_inv _ _ Hb') as (na' & b' & E' & _).
    exists (csubst a' 0 b). split; [|now apply tarity_lam].
    sq. eapply eval_fix' with (fn := substl (fix_subst mf) (dbody d)) (av := a');
      [exact Hguard|apply eval_atom; reflexivity|unfold cunfold_fix; rewrite E; reflexivity
      |now apply value_final|].
    rewrite Eb. eapply eval_beta; [apply eval_atom; reflexivity|now apply value_final|].
    rewrite E'. apply eval_atom. reflexivity.
  Qed.

  Lemma csubst_lift1 x d : closed x -> csubst x 0 (lift0 1 d) = d.
  Proof. intros cx. rewrite closed_subst //. now apply simpl_subst_k. Qed.

  Lemma eta_csubst dead j na xs F cs args av :
    eta_args dead j (na :: xs) args -> closed (mkApps F cs) -> closed av ->
    exists c args1,
      csubst av 0 (mk_lambdas xs (mkApps F (cs ++ args))) =
        mk_lambdas xs (mkApps F ((cs ++ [c]) ++ args1)) /\
      eta_args dead (S j) xs args1 /\ closed c /\ (c = av \/ (c = tBox /\ dead j)).
  Proof.
    intros H cl cav.
    rewrite csubst_mk_lambdas mkApps_app csubst_mkApps (csubst_closed _ _ (mkApps F cs)).
    { eapply closed_upwards; tea; lia. }
    inversion H; subst; cbn [map].
    - exists av, args0. erewrite eta_args_csubst; [|eassumption].
      cbn [csubst]. rewrite Nat.add_0_r Nat.compare_refl -app_assoc (mkApps_app F cs).
      repeat split; auto.
    - exists tBox, args0. erewrite eta_args_csubst; [|eassumption].
      cbn [csubst]. rewrite -app_assoc (mkApps_app F cs).
      repeat split; auto.
  Qed.

  (** *** Target head reductions *)

  Lemma value_tred t u : tred Σ' t u -> value Σ' t -> False.
  Proof.
    intros H v.
    assert (N : forall f args, args <> [] -> mkApps f args = t -> False).
    { intros f args nn E. destruct (exists_last nn) as (l & x & ->).
      rewrite mkApps_app in E. cbn in E. destruct H; discriminate. }
    destruct v as [t X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
    - destruct X as [t i|p ?].
      + destruct H; cbn in i; discriminate.
      + inversion H.
    - inversion H.
    - exact (N _ _ nn eq_refl).
  Qed.

  Lemma tred_csubst a j t u :
    closed a -> tred Σ' t u -> tred Σ' (csubst a j t) (csubst a j u).
  Proof.
    intros ca H.
    destruct H as [ind pars cdecl d c args brs br e cd cargs Hc Hn Hl1 Hl2
                  |ip d mfix idx args narg fn brs e cd Hcu cfn
                  |ip d v brs e cd cv]; cbn.
    - rewrite (csubst_closed a j d); [eapply closed_upwards; tea; lia|].
      rewrite /iota_red csubst_substl //. { rewrite forallb_rev forallb_skipn //. }
      rewrite List.length_rev Hl2.
      change (substl (List.rev (skipn pars args)) (csubst a (#|br.1| + j) br.2))
        with (iota_red pars args (br.1, csubst a (#|br.1| + j) br.2)).
      eapply tred_iota; tea. rewrite nth_error_map Hn //.
    - rewrite (csubst_closed a j d); [eapply closed_upwards; tea; lia|].
      rewrite (csubst_closed a j (mkApps fn args)); [eapply closed_upwards; tea; lia|].
      eapply tred_cofix; tea.
    - rewrite (csubst_closed a j d); [eapply closed_upwards; tea; lia|].
      rewrite (csubst_closed a j v); [eapply closed_upwards; tea; lia|].
      now constructor.
  Qed.

  Lemma eval_iota_cval Σ0 ind pars cdecl discr c args brs br res :
    eval Σ0 discr (cval ind c args) ->
    constructor_isprop_pars_decl Σ0 ind c = Some (false, pars, cdecl) ->
    nth_error brs c = Some br -> #|args| = pars + cstr_nargs cdecl ->
    #|skipn pars args| = #|br.1| -> eval Σ0 (iota_red pars args br) res ->
    eval Σ0 (tCase (ind, pars) discr brs) res.
  Proof.
    unfold cval. destruct with_constructor_as_block eqn:Hb; intros;
      [eapply eval_iota_block|eapply eval_iota]; eassumption.
  Qed.

  Lemma eval_proj_cval Σ0 p cdecl discr args a res :
    eval Σ0 discr (cval (proj_ind p) 0 args) ->
    constructor_isprop_pars_decl Σ0 (proj_ind p) 0 = Some (false, proj_npars p, cdecl) ->
    #|args| = proj_npars p + cstr_nargs cdecl ->
    nth_error args (proj_npars p + proj_arg p) = Some a ->
    eval Σ0 a res -> eval Σ0 (tProj p discr) res.
  Proof.
    unfold cval. destruct with_constructor_as_block eqn:Hb; intros;
      [eapply eval_proj_block|eapply eval_proj]; eassumption.
  Qed.

  Lemma eval_cval_inv Σ0 ind c args v :
    eval Σ0 (cval ind c args) v -> exists args', v = cval ind c args' /\ #|args'| = #|args|.
  Proof.
    unfold cval. destruct with_constructor_as_block eqn:Hb; intros ev.
    - eapply eval_Construct_inv in ev as (args' & -> & H).
      exists args'. split; [reflexivity|]. symmetry. exact (All2_length H).
    - eapply eval_mkApps_Construct_inv in ev as (args' & X); [|exact Hb]. destruct X as [_ -> H].
      exists args'. split; [reflexivity|]. symmetry. exact (All2_length H).
  Qed.

  Lemma cval_inj ind c args ind' c' args' :
    cval ind c args = cval ind' c' args' -> ind = ind' /\ c = c' /\ args = args'.
  Proof.
    unfold cval. destruct with_constructor_as_block.
    - now intros [= -> -> ->].
    - intros E. apply mkApps_eq_inj in E as [E ->]; try reflexivity. now injection E as -> ->.
  Qed.

  Lemma dead_head_construct ind c args : dead_head (mkApps (tConstruct ind c []) args) -> False.
  Proof. intros [(na & d & E)|(mf0 & idx0 & cs & E & _)]; head_contra E. Qed.

  Ltac cval_contra :=
    match goal with E : cval _ _ _ = _ |- _ => head_contra E end.

  Lemma tred_eval t u r : tred Σ' t u -> eval Σ' u r -> ∥ eval Σ' t r ∥.
  Proof.
    intros H ev.
    destruct H as [ind pars cdecl d c args brs br [e] cd cargs Hc Hn Hl1 Hl2
                  |ip d mfix idx args narg fn brs [e] cd Hcu cfn
                  |ip d v brs [e] cd cv]; sq.
    - eapply eval_iota_cval; [exact e|exact Hc|exact Hn|exact Hl1|exact Hl2|exact ev].
    - eapply eval_cofix_case; tea.
    - eapply eval_case_scrut; tea.
  Qed.

  (** *** Inversion of the relation at a target value *)

  Lemma value_lambda y b : value Σ' (tLambda y b).
  Proof. eapply eval_to_value; eapply eval_atom; reflexivity. Qed.

  Lemma R_value_elim (P : term -> term -> Prop) :
    (forall t w, Rh Σ' t w -> ∥ value Σ' w ∥ -> P t w) ->
    (forall ind c args w, R Σ' (cval ind c args) w -> P (cval ind c args) w) ->
    (forall y ys u t' s, R Σ' s (tLambda y (mk_lambdas ys u)) ->
       P s (tLambda y (mk_lambdas ys u)) -> tred Σ' t' u ->
       closed (tLambda y (mk_lambdas ys u)) -> closed (tLambda y (mk_lambdas ys t')) ->
       P s (tLambda y (mk_lambdas ys t'))) ->
    (forall x xs mf idx cs args t0 w,
       R Σ' (mkApps (tFix mf idx) cs) t0 -> ∥ eval Σ' t0 w ∥ -> tarity Σ' #|xs| w ->
       eta_args (param_dead mf idx) #|cs| (x :: xs) args ->
       closed (mkApps (tFix mf idx) cs) -> closed t0 -> closed w ->
       P (tLambda x (mk_lambdas xs (mkApps (tFix mf idx) (cs ++ args)))) w) ->
    forall t w, R Σ' t w -> ∥ value Σ' w ∥ -> P t w.
  Proof.
    intros Hh Hc He Hf.
    induction 1 as [t w H
                   |ind c args v0 mfix idx args' narg fn H IH e Hcu vv cl cl0
                   |t v0 t' H IH e cl cl0
                   |ys s u t' H IH Ht cu ct
                   |x xs mf idx cs args t0 w H IH e Ha He' cl cl0 clw]; intros [vw].
    - apply Hh; auto. now sq.
    - apply Hc. eapply R_cofix; tea.
    - destruct e as [e]. have E := eval_value _ _ vw e. subst. apply IH. now sq.
    - destruct ys as [|y ys]; cbn in *.
      + destruct (value_tred _ _ Ht vw).
      + eapply He; tea. apply IH. sq. apply value_lambda.
    - eapply Hf; tea.
  Qed.

  Lemma R_box_inv w : R Σ' tBox w -> ∥ value Σ' w ∥ -> w = tBox.
  Proof.
    intros H v.
    refine (R_value_elim (fun t w => t = tBox -> w = tBox) _ _ _ _ _ _ H v eq_refl).
    - intros t0 w0 H' _ ->. now inversion H'.
    - intros; first [discriminate | cval_contra].
    - intros y ys u t' s _ IH _ _ _ E. specialize (IH E). discriminate.
    - intros; first [discriminate | cval_contra].
  Qed.

  (** [expands w w0]: the target lambda [w] is [w0] with some head redexes
      under its lambdas not yet contracted (see [R_exp]). *)
  Inductive expands : term -> term -> Prop :=
  | expands_refl w : expands w w
  | expands_step y ys u t' w0 :
      expands (tLambda y (mk_lambdas ys u)) w0 -> tred Σ' t' u ->
      closed (tLambda y (mk_lambdas ys u)) -> closed (tLambda y (mk_lambdas ys t')) ->
      expands (tLambda y (mk_lambdas ys t')) w0.

  (** The source [fun na => b] is the eta-expansion of a fixpoint applied to
      [cs], and the target [w] is (an expansion of) the value [w0] of the
      corresponding partial application [t0]. *)
  Definition eta_state (na : name) (b w : term) : Prop :=
    exists xs mf idx cs args t0 w0,
      b = mk_lambdas xs (mkApps (tFix mf idx) (cs ++ args)) /\
      R Σ' (mkApps (tFix mf idx) cs) t0 /\ ∥ eval Σ' t0 w0 ∥ /\ tarity Σ' #|xs| w0 /\
      eta_args (param_dead mf idx) #|cs| (na :: xs) args /\
      closed (mkApps (tFix mf idx) cs) /\ closed t0 /\ closed w0 /\ expands w w0.

  Lemma R_lambda_inv na b w :
    R Σ' (tLambda na b) w -> ∥ value Σ' w ∥ -> closed (tLambda na b) ->
    (exists na' b', w = tLambda na' b' /\
      forall a a', R Σ' a a' -> closed a -> closed a' -> R Σ' (csubst a 0 b) (csubst a' 0 b')) \/
    eta_state na b w.
  Proof.
    intros H v.
    refine (R_value_elim (fun t w => forall na b, t = tLambda na b -> closed t ->
      (exists na' b', w = tLambda na' b' /\
        forall a a', R Σ' a a' -> closed a -> closed a' -> R Σ' (csubst a 0 b) (csubst a' 0 b')) \/
      eta_state na b w)
      _ _ _ _ _ _ H v _ _ eq_refl).
    - intros t0 w0 H' _ na0 b0 -> cl. inversion H'; subst.
      + left. eexists _, _; split; [reflexivity|]. intros. apply R_csubst; auto.
      + right.
        have cl' := R_closed _ _ _ 0 (R_head _ _ _ H') cl.
        cbn [closedn] in cl. rewrite closedn_mk_lambdas closedn_mkApps in cl.
        move/andP: cl => [cF _].
        replace (#|xs| + 1) with (0 + S #|xs|) in cF by lia.
        apply closedn_lift0_inv in cF. rewrite (lift_closed _ 0 _ cF).
        exists xs, mf, idx, [], args, (tFix mf' idx), (tFix mf' idx). cbn [app mkApps length].
        split; [reflexivity|]. split; [apply R_head; now constructor|].
        split; [sq; apply eval_atom; reflexivity|]. split; [now apply tarity_fix|].
        do 4 (split; [assumption|]). constructor.
    - intros; first [discriminate | cval_contra].
    - intros y ys u t' s _ IH Ht cu ct na0 b0 E cl.
      destruct (IH _ _ E cl) as [(na' & b' & E' & Hb)|St].
      + left. injection E' as <- <-.
        eexists _, _; split; [reflexivity|]. intros a a' Ha ca ca'.
        cbn in cu, ct.
        rewrite csubst_mk_lambdas. eapply (R_exp _ ys _ (csubst a' (#|ys| + 0) u)).
        * rewrite -csubst_mk_lambdas. apply Hb; auto.
        * apply tred_csubst; tea.
        * rewrite -csubst_mk_lambdas. apply closed_csubst; auto.
        * rewrite -csubst_mk_lambdas. apply closed_csubst; auto.
      + right. destruct St as (xs & mf & idx & cs & args & t0 & w0 & ? & ? & ? & ? & ? & ? & ? & ? & Hx).
        exists xs, mf, idx, cs, args, t0, w0.
        do 8 (split; [assumption|]). eapply expands_step; tea.
    - intros x xs mf idx cs args t0 w0 HR e Ha He cl cl0 clw na0 b0 E _.
      injection E as <- <-. right.
      exists xs, mf, idx, cs, args, t0, w0.
      split; [reflexivity|]. do 7 (split; [assumption|]). constructor.
  Qed.

  Lemma R_fix_inv mf idx w :
    R Σ' (tFix mf idx) w -> ∥ value Σ' w ∥ -> exists mf', w = tFix mf' idx /\ Rdefs Σ' mf mf'.
  Proof.
    intros H v.
    refine (R_value_elim (fun t w => forall mf idx, t = tFix mf idx ->
      exists mf', w = tFix mf' idx /\ Rdefs Σ' mf mf') _ _ _ _ _ _ H v _ _ eq_refl).
    - intros t0 w0 H' _ mf0 idx0 ->. inversion H'; subst; eauto.
    - intros; first [discriminate | cval_contra].
    - intros y ys u t' s _ IH _ _ _ mf0 idx0 E. destruct (IH _ _ E) as (? & ? & ?). discriminate.
    - intros; first [discriminate | cval_contra].
  Qed.

  Lemma R_lazy_inv b w :
    R Σ' (tLazy b) w -> ∥ value Σ' w ∥ -> exists b', w = tLazy b' /\ R Σ' b b'.
  Proof.
    intros H v.
    refine (R_value_elim (fun t w => forall b, t = tLazy b ->
      exists b', w = tLazy b' /\ R Σ' b b') _ _ _ _ _ _ H v _ eq_refl).
    - intros t0 w0 H' _ b0 ->. inversion H'; subst; eauto.
    - intros; first [discriminate | cval_contra].
    - intros y ys u t' s _ IH _ _ _ b0 E. destruct (IH _ E) as (? & ? & ?). discriminate.
    - intros; first [discriminate | cval_contra].
  Qed.

  Lemma dead_head_cofix mf idx args : dead_head (mkApps (tCoFix mf idx) args) -> False.
  Proof.
    have Hhd := mkApps_cofix_head mf idx args.
    intros [(na & d & E)|(mf0 & idx0 & cs & E & _)].
    - now rewrite E in Hhd.
    - apply (f_equal decompose_app) in E. rewrite !decompose_app_mkApps // in E.
  Qed.

  Lemma R_mkApps_cofix_inv mf idx args w :
    R Σ' (mkApps (tCoFix mf idx) args) w -> ∥ value Σ' w ∥ ->
    exists mf' args', w = mkApps (tCoFix mf' idx) args' /\ Rdefs Σ' mf mf' /\ Rs Σ' args args'.
  Proof.
    pose (Q := fun args t w => t = mkApps (tCoFix mf idx) args ->
      exists mf' args', w = mkApps (tCoFix mf' idx) args' /\ Rdefs Σ' mf mf' /\ Rs Σ' args args').
    assert (Hexp : forall args y ys u t' s, R Σ' s (tLambda y (mk_lambdas ys u)) ->
       Q args s (tLambda y (mk_lambdas ys u)) -> tred Σ' t' u ->
       closed (tLambda y (mk_lambdas ys u)) -> closed (tLambda y (mk_lambdas ys t')) ->
       Q args s (tLambda y (mk_lambdas ys t'))).
    { intros args0 y ys u t' s _ IH _ _ _ E.
      destruct (IH E) as (mf' & args' & E' & _).
      have Hhd := mkApps_cofix_head mf' idx args'. rewrite -E' in Hhd. destruct Hhd. }
    assert (Hfp : forall args x b w, Q args (tLambda x b) w).
    { intros args0 x b w0 E.
      have Hhd := mkApps_cofix_head mf idx args0. rewrite -E in Hhd. destruct Hhd. }
    revert w. induction args using rev_ind; intros w H v.
    - refine (R_value_elim (Q []) _ _ (Hexp []) _ _ _ H v eq_refl).
      + intros t0 w0 H' _ E. cbn in E. subst t0. inversion H'; subst.
        eexists _, []. cbn. repeat split; eauto. constructor.
      + intros ? ? ? ? ? E. head_contra E.
      + intros. apply Hfp.
    - refine (R_value_elim (Q (args ++ [x])) _ _ (Hexp _) _ _ _ H v eq_refl).
      + intros t0 w0 H' v0 E. subst t0. rewrite mkApps_app in H'. cbn in H'.
        have Hhd := mkApps_cofix_head mf idx args.
        inversion H'; subst.
        * destruct v0 as [v0].
          match goal with H : R _ (mkApps _ args) _ |- _ =>
            destruct (IHargs _ H) as (mf' & args' & -> & ? & ?) end.
          { sq. eapply value_app_head; tea. }
          eexists mf', (args' ++ [_]). rewrite mkApps_app. cbn. repeat split; eauto.
          apply Rs_app; auto. constructor; auto. constructor.
        * match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
        * match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
        * match goal with E : _ = mkApps _ args |- _ => rewrite -E in Hhd end. destruct Hhd.
        * match goal with D : dead_head _ |- _ => destruct (dead_head_cofix _ _ _ D) end.
      + intros ? ? ? ? ? E. head_contra E.
      + intros. apply Hfp.
  Qed.

  (** [n] arguments are not too many for constructor [c] of [ind]. *)
  Definition cbound (ind : inductive) (c n : nat) : Prop :=
    forall mdecl idecl cdecl,
      lookup_constructor Σ' ind c = Some (mdecl, idecl, cdecl) -> n <= cstr_arity mdecl cdecl.

  Lemma cfull_cbound ind c n : cfull Σ' ind c n -> cbound ind c n.
  Proof.
    intros (m & i & cd & Hl & ->) m' i' cd' Hl'. rewrite Hl in Hl'.
    injection Hl'; intros; subst. lia.
  Qed.

  (** A target value related to a constructor application is, up to
      unfolding cofixpoints, a constructor application; cofixpoints can only
      occur if the constructor has all its arguments. The first hypothesis
      is the case of the syntactic rules, which depends on the
      representation of constructor applications. *)
  Lemma R_construct_unfolds_gen ind c args :
    (forall w, Rh Σ' (cval ind c args) w -> ∥ value Σ' w ∥ -> closed w ->
       exists args', w = cval ind c args' /\ Rs Σ' args args') ->
    forall t w, R Σ' t w -> t = cval ind c args -> ∥ value Σ' w ∥ -> closed w ->
    exists args', unfolds Σ' w (cval ind c args') /\ Rs Σ' args args' /\
      ∥ value Σ' (cval ind c args') ∥ /\ closed (cval ind c args') /\
      (~ cfull Σ' ind c #|args| -> w = cval ind c args').
  Proof.
    intros Hh. induction 1; intros E vw clw.
    - subst. destruct (Hh _ ltac:(eassumption) vw clw) as (args' & -> & HR).
      exists args'. split; [constructor|]. split; [exact HR|]. split; [exact vw|].
      split; [exact clw|reflexivity].
    - apply cval_inj in E as (-> & -> & ->).
      destruct (IHR eq_refl) as (args'' & U & HR & vv & clv & _); auto.
      { match goal with H : ∥ eval _ _ v0 ∥ |- _ => destruct H as [e] end.
        sq. eapply eval_to_value; tea. }
      exists args''. split; [eapply unfolds_step; tea|]. split; [exact HR|].
      split; [exact vv|]. split; [exact clv|]. intros nf. contradiction.
    - destruct vw as [vw].
      match goal with H : ∥ eval _ _ _ ∥ |- _ => destruct H as [e] end.
      have E' := eval_value _ _ vw e. subst. apply IHR; auto. now sq.
    - destruct ys as [|y ys]; cbn in *.
      + destruct vw as [vw]. destruct (value_tred _ _ ltac:(eassumption) vw).
      + destruct (IHR E) as (args'' & U & _); auto.
        { sq. apply value_lambda. }
        inversion U; subst.
        * match goal with E : _ = cval _ _ _ |- _ => head_contra E end.
        * match goal with E : mkApps (tCoFix ?m ?i) ?a = tLambda _ _ |- _ =>
            have Hhd := mkApps_cofix_head m i a; rewrite E in Hhd; destruct Hhd end.
    - head_contra E.
  Qed.

  Lemma R_construct_unfolds ind c args w :
    cbound ind c #|args| -> R Σ' (cval ind c args) w -> ∥ value Σ' w ∥ -> closed w ->
    exists args', unfolds Σ' w (cval ind c args') /\ Rs Σ' args args' /\
      ∥ value Σ' (cval ind c args') ∥ /\ closed (cval ind c args') /\
      (~ cfull Σ' ind c #|args| -> w = cval ind c args').
  Proof.
    destruct with_constructor_as_block eqn:Hb.
    - intros _ H. eapply R_construct_unfolds_gen; [|exact H|reflexivity].
      intros w0 H' _ _. rewrite (cval_block _ _ _ Hb) in H'. inversion H'; subst.
      eexists; split; [now rewrite (cval_block _ _ _ Hb)|assumption].
    - revert w. induction args using rev_ind; intros w Hbd H.
      + eapply R_construct_unfolds_gen; [|exact H|reflexivity].
        intros w0 H' _ _. rewrite (cval_app _ _ _ Hb) in H'. cbn in H'. inversion H'; subst.
        match goal with X : Rs _ [] _ |- _ => inversion X; subst end.
        exists []. split; [now rewrite (cval_app _ _ _ Hb)|constructor].
      + eapply R_construct_unfolds_gen; [|exact H|reflexivity].
        intros w0 H' [v0] cw0. rewrite (cval_app _ _ _ Hb) mkApps_app in H'. cbn in H'.
        inversion H'; subst.
        all: try (match goal with E : _ = mkApps (tConstruct _ _ _) _ |- _ => head_contra E end).
        all: try (match goal with D : dead_head _ |- _ => destruct (dead_head_construct _ _ _ D) end).
        match goal with HR : R _ (mkApps _ _) ?f', IH : forall w, cbound _ _ _ -> _ |- _ =>
          rewrite -(cval_app _ _ _ Hb) in HR;
          destruct (IH f') as (args' & _ & HR' & _ & _ & Enf); [|exact HR| | |] end.
        * intros m i cd Hl. specialize (Hbd _ _ _ Hl). rewrite length_app in Hbd. cbn in Hbd. lia.
        * sq. eapply value_app_head; tea.
        * move: cw0. cbn. now move/andP => [].
        * rewrite Enf.
          { intros (m & i & cd & Hl & En). specialize (Hbd _ _ _ Hl).
            rewrite length_app in Hbd. cbn in Hbd. lia. }
          exists (args' ++ [a']). split; [rewrite !(cval_app _ _ _ Hb) mkApps_app //|].
          apply Rs_app; auto. constructor; auto. constructor.
  Qed.

  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall kn b, declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σ' kn {| cst_body := Some b' |} /\ R Σ' b b'.
  Hypothesis HclΣ : closed_env Σ.
  Hypothesis HclΣ' : closed_env Σ'.

  Lemma cfull_Hind ind c n : cfull Σ ind c n -> cfull Σ' ind c n.
  Proof.
    unfold cfull. now rewrite (ELiftConstants.same_lookup_constructor _ _ Hind).
  Qed.

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
      + rewrite isConstructApp_mkApps.
        change (isConstructApp (tConstruct ind c [])) with true.
        rewrite !orb_true_r. cbn. intros; discriminate.
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
      eapply eval_cval_inv in ev as (args'' & -> & Hlen).
      eapply R_cofix; tea; first [now rewrite Hlen | now sq].
    - destruct (IHR v ev Hh) as (v0' & [e0] & Hv).
      match goal with H : ∥ eval _ _ v0 ∥ |- _ => destruct H as [e1] end.
      have E : v0 = v0' by (eapply eval_value; [eapply eval_to_value; exact e1|exact e0]).
      subst v0'. exists v0. split; [now sq|auto].
    - destruct (IHR v ev Hh) as (v0' & [e0] & Hv).
      destruct ys as [|y ys]; cbn in *.
      + destruct (tred_eval _ _ _ ltac:(eassumption) e0) as [e']. exists v0'. split; [now sq|auto].
      + apply eval_lambda_inv in e0. subst v0'.
        eexists; split; [sq; apply eval_atom; reflexivity|].
        match goal with Ht : tred _ ?t' ?u |- _ =>
          exact (R_exp _ (y :: ys) _ u t' Hv Ht ltac:(assumption) ltac:(assumption)) end.
    - apply eval_lambda_inv in ev. subst v.
      match goal with H : ∥ eval _ t0 w ∥ |- _ => destruct H as [e1] end.
      exists w. split; [sq; apply value_final; eapply eval_to_value; exact e1|].
      eapply R_fix_part; tea. now sq.
  Qed.

  Lemma exp_goal ys u t' v :
    tred Σ' t' u -> closed (mk_lambdas ys u) -> closed (mk_lambdas ys t') ->
    goal (mk_lambdas ys u) v -> goal (mk_lambdas ys t') v.
  Proof.
    intros Ht cu ct (v0 & [e] & Hv). destruct ys as [|y ys]; cbn in *.
    - destruct (tred_eval _ _ _ Ht e) as [e']. exists v0. split; [now sq|auto].
    - apply eval_lambda_inv in e. subst v0.
      eexists; split; [sq; apply eval_atom; reflexivity|].
      exact (R_exp _ (y :: ys) _ u t' Hv Ht cu ct).
  Qed.

  Lemma expands_app w w0 a' s :
    expands w w0 -> closed a' -> ∥ value Σ' a' ∥ -> goal (tApp w0 a') s -> goal (tApp w a') s.
  Proof.
    intros H ca' [va']. induction H as [w|y ys u t' w0 H IH Ht cu ct]; auto.
    intros G. destruct (IH G) as (r1 & [e1] & HR1).
    destruct (eval_app_lambda_inv Hguard Hprop Σ' HclΣ' _ _ _ _ _ e1
                (eval_atom Σ' (tLambda y (mk_lambdas ys u)) eq_refl)) as (av & ea & eb).
    have E := eval_value _ _ va' ea. subst av.
    cbn in cu, ct.
    rewrite csubst_mk_lambdas in eb.
    destruct (exp_goal ys (csubst a' (#|ys| + 0) u) (csubst a' (#|ys| + 0) t') s)
      as (r & [e2] & HR2).
    - apply tred_csubst; tea.
    - rewrite -csubst_mk_lambdas. apply closed_csubst; auto.
    - rewrite -csubst_mk_lambdas. apply closed_csubst; auto.
    - exists r1. split; [now sq|exact HR1].
    - exists r. split; [|exact HR2]. sq.
      eapply eval_beta; [apply eval_atom; reflexivity|now apply value_final|].
      rewrite csubst_mk_lambdas. exact e2.
  Qed.

  (** Application of related functions: either the target is a lambda with a
      related body, or the source is the eta-expansion of a fixpoint whose
      partial application the target has already evaluated. *)
  Lemma beta_sim na b w av a' res :
    R Σ' (tLambda na b) w -> ∥ value Σ' w ∥ -> closed (tLambda na b) ->
    R Σ' av a' -> closed av -> closed a' -> ∥ value Σ' a' ∥ ->
    eval Σ (csubst av 0 b) res ->
    (forall t', R Σ' (csubst av 0 b) t' -> goal t' res) ->
    goal (tApp w a') res.
  Proof.
    intros Hw vw cl Ha cav ca' [va'] ev K.
    destruct (R_lambda_inv _ _ _ Hw vw cl) as [(na' & b' & -> & Hb)|St].
    - destruct (K _ (Hb _ _ Ha cav ca')) as (w3 & [e3] & H3).
      exists w3. split; [|exact H3]. sq.
      eapply eval_beta; [apply eval_atom; reflexivity|now apply value_final|exact e3].
    - destruct St as (xs & mf & idx & cs & args & t0 & w0 & -> & HR & [e0] & Har & Hargs
                      & clF & cl0 & clw0 & Hx).
      eapply expands_app; [exact Hx|exact ca'|now sq|].
      destruct (eta_csubst _ _ _ _ _ _ _ av Hargs clF cav) as (c & args1 & E & Hargs1 & cc & Hc).
      rewrite E in ev, K.
      have HRc : R Σ' (tApp (mkApps (tFix mf idx) cs) c) (tApp t0 a').
      { destruct Hc as [->|[-> D]]; apply R_head.
        - apply Rh_app; auto.
        - apply Rh_app_dead; [exact HR| |exact clF|exact cl0|exact ca'|now sq].
          right. exists mf, idx, cs. split; [reflexivity|exact D]. }
      have ccl : closed (tApp (mkApps (tFix mf idx) cs) c) by (cbn; rewrite clF cc //).
      have ctl : closed (tApp t0 a') by (cbn; rewrite cl0 ca' //).
      destruct xs as [|y ys].
      + inversion Hargs1; subst. cbn [mk_lambdas] in K.
        rewrite app_nil_r mkApps_app in K. cbn [mkApps] in K.
        destruct (K _ HRc) as (w3 & [e3] & H3).
        destruct (eval_app_inv Hguard Hprop Σ' HclΣ' _ _ _ e3) as (fv & ef & e3').
        have E0 := eval_deterministic ef e0. subst fv.
        exists w3. split; [now sq|exact H3].
      + cbn [mk_lambdas] in ev. apply eval_lambda_inv in ev. subst res.
        cbn [length tarity] in Har.
        destruct (Har a' ca' ltac:(now sq)) as (w3 & [e3] & Har3).
        exists w3. split; [now sq|].
        have e3' : eval Σ' (tApp t0 a') w3
          by exact (eval_app_value Hguard Hprop Σ' HclΣ' _ _ _ _ e0 e3).
        eapply (R_fix_part _ y ys mf idx (cs ++ [c]) args1 (tApp t0 a') w3).
        * rewrite mkApps_app. exact HRc.
        * now sq.
        * exact Har3.
        * rewrite length_app /= Nat.add_1_r. exact Hargs1.
        * rewrite mkApps_app. exact ccl.
        * exact ctl.
        * eapply eval_closed; [exact HclΣ'|exact ctl|exact e3'].
  Qed.

  Lemma closed_case_scrut ys ip X Y B :
    closed X -> closed (mk_lambdas ys (tCase ip Y B)) -> closed (mk_lambdas ys (tCase ip X B)).
  Proof.
    intros cX. rewrite !closedn_mk_lambdas. cbn. move/andP => [_ ->].
    rewrite andb_true_r. eapply closed_upwards; tea. lia.
  Qed.

  Lemma unfolds_exp ys ip B w v res :
    unfolds Σ' w v -> closed w -> closed (mk_lambdas ys (tCase ip w B)) ->
    goal (mk_lambdas ys (tCase ip v B)) res -> goal (mk_lambdas ys (tCase ip w B)) res.
  Proof.
    induction 1 as [|mfix idx args narg fn v0 v Hcu [vv] [e1] U IH]; intros cw cT G; auto.
    have cfn : closed (mkApps fn args).
    { move: cw. rewrite !closedn_mkApps. move/andP => [x1 x2]. apply/andP; split; auto.
      eapply closed_cunfold_cofix; tea. }
    have cv0 := eval_closed Σ' HclΣ' _ _ cfn e1.
    eapply (exp_goal ys (tCase ip (mkApps fn args) B)).
    - eapply tred_cofix; tea. sq. now apply value_final.
    - eapply closed_case_scrut; [exact cfn|exact cT].
    - exact cT.
    - eapply (exp_goal ys (tCase ip v0 B)).
      + apply tred_scrut; auto. now sq.
      + eapply closed_case_scrut; [exact cv0|exact cT].
      + eapply closed_case_scrut; [exact cfn|exact cT].
      + apply IH; auto. eapply closed_case_scrut; [exact cv0|exact cT].
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
    (forall f' a', a = tBox -> R Σ' f f' -> dead_head f -> closed f' -> closed a' ->
      ∥ value Σ' a' ∥ -> goal (tApp f' a') res) ->
    Rh Σ' (tApp f a) t0 -> goal t0 res.
  Proof.
    intros cl Hc Hb Hd Ht. split_cl cl c1 c2. inversion Ht; subst.
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
    - apply Hd; auto.
  Qed.

  Ltac dead_contra D c1 ev1 :=
    let i := fresh "i" in
    destruct (dead_head_eval Hguard Hprop Σ HclΣ _ _ c1 D ev1)
      as [(? & ? & E)|(? & ? & _ & E & _)];
    try discriminate E;
    match goal with i : is_true (negb _) |- _ =>
      rewrite E Hguard in i; cbn in i; discriminate i end.

  Ltac vof e := sq; eapply eval_to_value; exact e.

  (** The case of a match on a constructor, for both representations of
      constructor applications. *)
  Lemma sim_iota ind pars cdecl discr c args brs br res t0 :
    eval Σ discr (cval ind c args) ->
    (closed discr -> forall t', Rh Σ' discr t' -> goal t' (cval ind c args)) ->
    constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
    nth_error brs c = Some br -> #|args| = pars + cstr_nargs cdecl ->
    #|skipn pars args| = #|br.1| ->
    eval Σ (iota_red pars args br) res ->
    (closed (iota_red pars args br) ->
     forall t', Rh Σ' (iota_red pars args br) t' -> goal t' res) ->
    closed (tCase (ind, pars) discr brs) -> Rh Σ' (tCase (ind, pars) discr brs) t0 ->
    goal t0 res.
  Proof.
    intros ev1 IHev1 e1 e2 e3 e4 ev2 IHev2 cl Ht.
    have Hfull : cfull Σ' ind c #|args|.
    { eapply cfull_isprop; [|exact e3].
      rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); exact e1. }
    have Hbnd := cfull_cbound _ _ _ Hfull.
    tgt_closed Ht cl cl0. inversion Ht; subst.
    - (* congruence *)
      have cl' := cl. split_cl cl c1 c2. split_cl cl0 c1' c2'.
      sim_ev ev1 w ee5 Hw; [auto|].
      have cw := eval_closed Σ' HclΣ' _ _ c1' ee5.
      have cargs := eval_closed Σ HclΣ _ _ c1 ev1. rewrite closedn_cval in cargs.
      destruct (R_construct_unfolds _ _ _ _ Hbnd Hw) as (args' & U & Hargs & [vv] & clv & _);
        [sq; eapply eval_to_value; tea|auto|].
      rewrite closedn_cval in clv.
      match goal with HR : Rbrs _ ?brs ?brs', Hn : nth_error ?brs _ = Some _ |- _ =>
        destruct (Rbrs_nth_error _ _ _ _ _ HR Hn) as (br' & Hn' & Hb1 & Hb2) end.
      match type of ev2 with eval _ (iota_red ?pars _ _) _ =>
        sim_ev_with ev2 (iota_red pars args' br') w3 ee6 Hw3;
        [eapply closed_iota_red; tea | apply R_iota_red; auto | ] end.
      exists w3. split; [|auto].
      match goal with |- ∥ eval _ (tCase ?ip _ ?brs') _ ∥ =>
        match type of U with unfolds _ _ ?k =>
          assert (ev' : eval Σ' (tCase ip k brs') w3) end end.
      { eapply eval_iota_cval;
          [ apply value_final; exact vv
          | rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); eassumption
          | exact Hn' | rewrite -(Rs_length _ _ _ Hargs); eassumption
          | rewrite -Hb1 -(Rs_length _ _ _ (Rs_skipn _ _ _ _ Hargs)); eassumption
          | exact ee6]. }
      destruct (unfolds_case _ _ _ _ _ _ U ev') as [ev'']. sq.
      eapply eval_case_scrut; tea.
    - (* identity case *)
      split_cl cl c1 c2.
      sim_ev ev1 w ee5 Hw; [auto|].
      exists w. split; [now sq|].
      have cargs := eval_closed Σ HclΣ _ _ c1 ev1. rewrite closedn_cval in cargs.
      match goal with H : #|skipn 0 _| = _ |- _ => rewrite skipn_0 in H end.
      match type of ev2 with eval _ _ ?r => match type of ev1 with eval _ _ ?k =>
        enough (E : r = k) by (rewrite E; exact Hw) end end.
      eapply case_id_iota with (Σ := Σ); tea.
      * eapply all_rebuild_nth; tea.
      * eapply eval_to_value; exact ev1.
    - (* case_fun *)
      have cl' := cl. split_cl cl c1 c2.
      match goal with |- goal (mk_lambdas ?a (tCase _ (lift0 _ ?b) (map _ ?c))) _ =>
        rename a into ys1; rename b into d1; rename c into brsx end.
      assert (HRd : R Σ' discr d1) by assumption.
      assert (HRb : Rbrs Σ' (map (fun br => (br.1, strip_lambdas #|ys1| br.2)) brs) brsx)
        by assumption.
      assert (Hhl : forallb (fun br => has_lambdas #|ys1| br.2) brs) by assumption.
      have cd' := R_closed _ _ _ 0 HRd c1.
      destruct (sim_layer _ _ ev1 (IHev1 c1) _ HRd) as (w & [ee5] & Hw).
      have cw := eval_closed Σ' HclΣ' _ _ cd' ee5.
      have cargs := eval_closed Σ HclΣ _ _ c1 ev1. rewrite closedn_cval in cargs.
      destruct (R_construct_unfolds _ _ _ _ Hbnd Hw ltac:(vof ee5) cw)
        as (args' & U & Hargs & [vv] & clvc & _).
      have clv := clvc. rewrite closedn_cval in clv.
      have Hn1 : nth_error (map (fun br => (br.1, strip_lambdas #|ys1| br.2)) brs) c
                 = Some (br.1, strip_lambdas #|ys1| br.2) by (rewrite nth_error_map e2 //).
      destruct (Rbrs_nth_error _ _ _ _ _ HRb Hn1) as (br1 & Hn' & Hb1 & Hb2).
      cbn in Hb1, Hb2.
      have hl : has_lambdas #|ys1| br.2
        by exact (proj1 (forallb_forall _ _) Hhl _ (nth_error_In _ _ e2)).
      have Esrc : iota_red pars args br =
        mk_lambdas (lambda_names #|ys1| br.2)
          (substl_at #|ys1| (List.rev (skipn pars args)) (strip_lambdas #|ys1| br.2)).
      { rewrite /iota_red. rewrite {1}(mk_lambdas_strip _ _ hl). rewrite substl_mk_lambdas.
        rewrite (length_lambda_names_has _ _ hl). reflexivity. }
      have clsrc : closed (iota_red pars args br) by (eapply closed_iota_red; tea).
      have cargs' : forallb (closedn 0) (List.rev (skipn pars args'))
        by rewrite forallb_rev forallb_skipn //.
      have HR2 : R Σ' (iota_red pars args br)
        (mk_lambdas ys1 (substl_at #|ys1| (List.rev (skipn pars args')) br1.2)).
      { rewrite Esrc. apply R_mk_lambdas; [apply length_lambda_names_has; auto|].
        apply R_substl_at; auto; [apply Rs_rev, Rs_skipn; auto|].
        rewrite forallb_rev forallb_skipn //. }
      destruct (sim_layer _ _ ev2 (IHev2 clsrc) _ HR2) as (w3 & [ee6] & Hw3).
      have cT2 := R_closed _ _ _ 0 HR2 clsrc.
      rewrite (lift_closed _ _ _ cd') in cl0 |- *.
      set (B := map _ brsx) in *.
      have clT : forall X, closed X -> closed (mk_lambdas ys1 (tCase (ind, pars) X B))
        by (intros X cX; eapply closed_case_scrut; [exact cX|exact cl0]).
      eapply (exp_goal ys1 (tCase (ind, pars) w B));
        [apply tred_scrut; [now sq|auto|auto] | apply clT; auto | apply clT; auto | ].
      eapply unfolds_exp; [exact U | exact cw | apply clT; auto |].
      have L : #|br1.1| = #|List.rev (skipn pars args')|.
      { rewrite List.length_rev -Hb1 -(Rs_length _ _ _ (Rs_skipn _ _ _ _ Hargs)). symmetry; exact e4. }
      have Eb : iota_red pars args' (br1.1, exchange #|ys1| #|br1.1| 0 br1.2) =
                substl_at #|ys1| (List.rev (skipn pars args')) br1.2.
      { rewrite /iota_red. cbn. rewrite -substl_at_0.
        rewrite L substl_at_exchange // Nat.add_0_r //. }
      eapply (exp_goal ys1 (substl_at #|ys1| (List.rev (skipn pars args')) br1.2));
        [ | exact cT2 | apply clT; auto | exists w3; split; [now sq|auto] ].
      rewrite -Eb. eapply tred_iota.
      * sq. apply value_final. exact vv.
      * exact clvc.
      * exact clv.
      * rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); eassumption.
      * subst B. rewrite nth_error_map Hn' //.
      * rewrite -(Rs_length _ _ _ Hargs); eassumption.
      * cbn. rewrite -Hb1 -(Rs_length _ _ _ (Rs_skipn _ _ _ _ Hargs)). exact e4.
  Qed.

  (** The case of a projection out of a constructor, likewise. *)
  Lemma sim_proj p cdecl discr args a res t0 :
    eval Σ discr (cval (proj_ind p) 0 args) ->
    (closed discr -> forall t', Rh Σ' discr t' -> goal t' (cval (proj_ind p) 0 args)) ->
    constructor_isprop_pars_decl Σ (proj_ind p) 0 = Some (false, proj_npars p, cdecl) ->
    #|args| = proj_npars p + cstr_nargs cdecl ->
    nth_error args (proj_npars p + proj_arg p) = Some a ->
    eval Σ a res -> (closed a -> forall t', Rh Σ' a t' -> goal t' res) ->
    closed (tProj p discr) -> Rh Σ' (tProj p discr) t0 -> goal t0 res.
  Proof.
    intros ev1 IHev1 e1 e2 e3 ev2 IHev2 cl Ht.
    have Hfull : cfull Σ' (proj_ind p) 0 #|args|.
    { eapply cfull_isprop; [|exact e2].
      rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); exact e1. }
    have Hbnd := cfull_cbound _ _ _ Hfull.
    tgt_closed Ht cl cl0. inversion Ht; subst.
    cbn in cl, cl0.
    sim_ev ev1 w ee0 Hw; [auto|].
    have cw := eval_closed Σ' HclΣ' _ _ cl0 ee0.
    have cargs := eval_closed Σ HclΣ _ _ cl ev1. rewrite closedn_cval in cargs.
    destruct (R_construct_unfolds _ _ _ _ Hbnd Hw) as (args' & U & Hargs & [vv] & clv & _);
      [sq; eapply eval_to_value; tea|auto|].
    match goal with Hn : nth_error _ _ = Some _ |- _ =>
      destruct (Rs_nth_error _ _ _ _ _ Hargs Hn) as (a' & Hn' & Ha');
      have ca := nth_error_forallb Hn cargs end.
    sim_ev_with ev2 a' w3 ee3 Hw3; [exact ca|exact Ha'|].
    exists w3. split; [|auto].
    match goal with |- ∥ eval _ (tProj ?p _) _ ∥ =>
      match type of U with unfolds _ _ ?k =>
        assert (ev' : eval Σ' (tProj p k) w3) end end.
    { eapply eval_proj_cval;
        [ apply value_final; exact vv
        | rewrite -(ELiftConstants.same_constructor_isprop_pars_decl _ _ Hind); eassumption
        | rewrite -(Rs_length _ _ _ Hargs); eassumption
        | exact Hn' | exact ee3]. }
    destruct (unfolds_proj _ _ _ _ _ U ev') as [ev'']. sq.
    eapply eval_proj_scrut; tea.
  Qed.

  Lemma simulation_head t v (ev : eval Σ t v) :
    closed t -> forall t', Rh Σ' t t' -> goal t' v.
  Proof.
    induction ev using eval_rect; intros cl t0 Ht.
    all: try (exfalso; unfold is_true in *; congruence).
    - (* box *)
      eapply app_head; [exact cl| | | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. discriminate. }
      2:{ intros f' a' -> Hf D c1' c2' va'. split_cl cl c1 c2. dead_contra D c1 ev1. }
      intros f' a' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      apply R_box_inv in Hw; [subst|vof ee0].
      exists tBox. split; [sq; eapply eval_box; tea|apply R_refl].
    - (* beta *)
      eapply app_head; [exact cl| | | |exact Ht].
      3:{ intros f' a0' -> Hf D c1' c2' va0'. split_cl cl c1 c2.
          have E := eval_deterministic ev2 (eval_atom Σ tBox eq_refl). subst a'.
          destruct (dead_head_eval Hguard Hprop Σ HclΣ _ _ c1 D ev1)
            as [(na0 & d0 & E)|(? & ? & _ & E & _)]; [|discriminate E].
          injection E as -> ->.
          rewrite (csubst_lift1 tBox) // in ev3, IHev3.
          sim_ev ev1 w ee0 Hw; [auto|].
          have clam := eval_closed Σ HclΣ _ _ c1 ev1.
          destruct (beta_sim _ _ w a0' a0' res Hw ltac:(vof ee0) clam (R_refl _ _) c2' c2' va0')
            as (w3 & [e3] & H3).
          { rewrite csubst_lift1 //. }
          { rewrite csubst_lift1 //. intros t' Ht'. apply (sim_layer _ _ ev3); auto.
            apply IHev3. move: clam. cbn. intros clam.
            rewrite -(csubst_lift1 tBox d0) //. apply closed_csubst; auto. }
          exists w3. split; [|exact H3]. sq.
          exact (eval_app_value Hguard Hprop Σ' HclΣ' _ _ _ _ ee0 e3). }
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
      have cw2 := eval_closed Σ' HclΣ' _ _ c2' ee2.
      have ca' := eval_closed Σ HclΣ _ _ c2 ev2.
      have clam := eval_closed Σ HclΣ _ _ c1 ev1.
      destruct (beta_sim _ _ w a' w2 res Hw ltac:(vof ee0) clam Hw2 ca' cw2 ltac:(vof ee2) ev3)
        as (w3 & [e3] & H3).
      { intros t' Ht'. apply (sim_layer _ _ ev3); auto. apply IHev3.
        cbn in clam. apply closed_csubst; auto. }
      exists w3. split; [|exact H3]. sq.
      eapply eval_app_value; [exact Hguard|exact Hprop|exact HclΣ'|exact ee0|].
      eapply eval_app_arg; [exact Hguard|exact Hprop|exact HclΣ'|exact ee2|exact e3].
    - (* zeta *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      + split_cl cl c1 c2. split_cl cl0 c1' c2'.
        sim_ev ev1 w ee0 Hw; [auto|].
        have cw := eval_closed Σ' HclΣ' _ _ c1' ee0.
        have cb0' := eval_closed Σ HclΣ _ _ c1 ev1.
        match type of ev2 with eval _ (csubst _ 0 ?b1) _ =>
          match goal with HR : R _ b1 ?b1' |- _ =>
          sim_ev_with ev2 (csubst w 0 b1') w3 ee3 Hw3;
          [apply closed_csubst; auto | apply R_csubst; auto | ] end end.
        exists w3. split; [sq; eapply eval_zeta; tea|auto].
      + (* let_inline *)
        split_cl cl c1 c2.
        match goal with |- goal (subst1 ?a 0 ?c) _ => rename a into v1; rename c into e1 end.
        match goal with HRv : R _ _ v1 |- _ => rename HRv into Hv1 end.
        have cv' := R_closed _ _ _ 0 Hv1 c1.
        sim_ev ev1 w ee0 Hw; [auto|].
        have cw := eval_closed Σ' HclΣ' _ _ cv' ee0.
        have cb0' := eval_closed Σ HclΣ _ _ c1 ev1.
        match type of ev1 with eval _ _ ?x =>
          have Hv2 : R Σ' x v1 by (eapply R_eval; [exact Hw|sq; exact ee0|auto|auto]) end.
        match type of ev2 with eval _ (csubst _ 0 ?b1) _ =>
          match goal with HR : R _ b1 e1 |- _ =>
          have ce1 := R_closed _ _ _ 1 HR c2;
          sim_ev_with ev2 (csubst v1 0 e1) w3 ee3 Hw3;
          [apply closed_csubst; auto | apply R_csubst; auto | ] end end.
        exists w3. split; [|auto]. unfold subst1. rewrite -closed_subst //; now sq.
    - (* iota *)
      match goal with H : with_constructor_as_block = _ |- _ =>
        rewrite <- (cval_app _ _ _ H) in ev1, IHev1 end.
      eapply sim_iota; eassumption.
    - (* iota block *)
      match goal with H : with_constructor_as_block = _ |- _ =>
        rewrite <- (cval_block _ _ _ H) in ev1, IHev1 end.
      eapply sim_iota; eassumption.
    - (* fix' *)
      eapply app_head; [exact cl| | | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. discriminate. }
      2:{ intros f' a0' -> Hf D c1' c2' va0'. split_cl cl c1 c2.
          have E := eval_deterministic ev2 (eval_atom Σ tBox eq_refl). subst av.
          destruct (dead_head_eval Hguard Hprop Σ HclΣ _ _ c1 D ev1)
            as [(? & ? & E)|(mf0 & idx0 & _ & E & P)]; [discriminate E|].
          injection E as <- <-.
          sim_ev ev1 w ee0 Hw; [auto|].
          apply R_fix_inv in Hw as (mf' & -> & Hmf); [|vof ee0].
          have cfx := eval_closed Σ' HclΣ' _ _ c1' ee0.
          have cfs := eval_closed Σ HclΣ _ _ c1 ev1.
          edestruct R_cunfold_fix as (fn' & Hfn' & HRfn); [exact Hmf|exact cfs|exact cfx|eassumption|].
          match goal with Hcu : cunfold_fix _ _ = Some (_, fn) |- _ => rename Hcu into ecu end.
          have cfn := closed_cunfold_fix _ _ _ _ cfs ecu.
          have cfn' := closed_cunfold_fix _ _ _ _ cfx Hfn'.
          have Dfn : dead_head fn.
          { left. destruct P as (d & Hd & Dd). unfold cunfold_fix in ecu. rewrite Hd in ecu.
            injection ecu as _ <-. apply deadlam_substl; [|exact Dd].
            now apply (closed_fix_subst' _ idx). }
          destruct (IHev3 ltac:(cbn; rewrite cfn //) (tApp fn' a0')) as (w3 & [e3] & H3).
          { apply Rh_app_dead; auto. }
          destruct va0' as [va0'].
          exists w3. split; [|exact H3]. sq.
          eapply eval_fix'; [exact Hguard|exact ee0|exact Hfn'|now apply value_final|exact e3]. }
      intros f' a0' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      apply R_fix_inv in Hw as (mf' & -> & Hmf); [|vof ee0].
      have cfx := eval_closed Σ' HclΣ' _ _ c1' ee0.
      have cfs := eval_closed Σ HclΣ _ _ c1 ev1.
      edestruct R_cunfold_fix as (fn' & Hfn' & HRfn); [exact Hmf|exact cfs|exact cfx|eassumption|].
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
        match type of ev1 with eval _ ?s0 (mkApps ?h _) =>
          assert (csf : closed h) by
            (assert (X : closed s0) by assumption; have := eval_closed Σ HclΣ _ _ X ev1;
             rewrite closedn_mkApps; move/andP => [x1 _]; exact x1) end.
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact csf|exact cw1|eassumption|].
        clear csf.
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
        match type of ev1 with eval _ ?s0 (mkApps ?h _) =>
          assert (csf : closed h) by
            (assert (X : closed s0) by assumption; have := eval_closed Σ HclΣ _ _ X ev1;
             rewrite closedn_mkApps; move/andP => [x1 _]; exact x1) end.
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact csf|exact cw1|eassumption|].
        clear csf.
        match type of ev2 with eval _ (tCase _ ?d _) _ => assert (csrc : closed d) end.
        { have := eval_closed Σ HclΣ _ _ c1 ev1. rewrite !closedn_mkApps.
          move/andP => [x1 x2]. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
        sim_ev_with ev2 (mkApps fn' args') w3 ee3 Hw3.
        { cbn. apply/andP; split; auto. }
        { apply R_head; apply Rh_case_id; auto. apply R_mkApps; auto. }
        edestruct case_id_result as (cc & argsc & E & Hfull); [..|exact ev2|reflexivity|exact csrc|eassumption|]; tea.
        have Hfull' := cfull_Hind _ _ _ Hfull.
        rewrite E in Hw3 |- *.
        exists (mkApps (tCoFix mf' idx) args'). split; [now sq|].
        eapply R_cofix; tea.
        * now sq.
        * sq. eapply eval_to_value; tea.
        * eapply eval_closed; [exact HclΣ'| |exact ee3].
          rewrite closedn_mkApps. apply/andP; split; auto. eapply closed_cunfold_cofix; tea.
      + (* case_fun *)
        split_cl cl c1 c2.
        match goal with |- goal (mk_lambdas ?a (tCase _ (lift0 _ ?b) (map _ ?c))) _ =>
          rename a into ys1; rename b into d1; rename c into brsx end.
        assert (HRd : R Σ' discr d1) by assumption.
        have cd' := R_closed _ _ _ 0 HRd c1.
        destruct (sim_layer _ _ ev1 (IHev1 c1) _ HRd) as (w & [ee0] & Hw).
        apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
        have cw := eval_closed Σ' HclΣ' _ _ cd' ee0.
        rewrite closedn_mkApps in cw. move/andP: cw => [cw1 cw2].
        match type of ev1 with eval _ ?s0 (mkApps ?h _) =>
          assert (csf : closed h) by
            (assert (X : closed s0) by assumption; have := eval_closed Σ HclΣ _ _ X ev1;
             rewrite closedn_mkApps; move/andP => [x1 _]; exact x1) end.
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact csf|exact cw1|eassumption|].
        clear csf.
        assert (csrc : closed (mkApps fn args)).
        { have := eval_closed Σ HclΣ _ _ c1 ev1. rewrite !closedn_mkApps.
          move/andP => [x1 x2]. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
        have cfn' : closed (mkApps fn' args').
        { rewrite closedn_mkApps. apply/andP; split; auto. eapply closed_cunfold_cofix; tea. }
        have HR2 : Rh Σ' (tCase ip (mkApps fn args) brs)
          (mk_lambdas ys1 (tCase ip (lift0 #|ys1| (mkApps fn' args'))
             (map (fun br => (br.1, exchange #|ys1| #|br.1| 0 br.2)) brsx))).
        { apply Rh_case_fun; auto. apply R_mkApps; auto. }
        destruct (IHev2 ltac:(cbn; apply/andP; split; auto) _ HR2) as (w3 & [ee3] & Hw3).
        rewrite (lift_closed _ _ _ cfn') in ee3. rewrite (lift_closed _ _ _ cd') in cl0 |- *.
        eapply exp_goal;
          [eapply tred_cofix; [sq; exact ee0|exact cd'|exact Hfn'|exact cfn']
          | eapply closed_case_scrut; [exact cfn'|exact cl0] | exact cl0
          | exists w3; split; [now sq|auto]].
    - (* cofix proj *)
      tgt_closed Ht cl cl0. inversion Ht; subst.
      cbn in cl, cl0.
      sim_ev ev1 w ee0 Hw; [auto|].
      apply R_mkApps_cofix_inv in Hw as (mf' & args' & -> & Hmf & Hargs); [|vof ee0].
      have cw := eval_closed Σ' HclΣ' _ _ cl0 ee0.
      rewrite closedn_mkApps in cw. move/andP: cw => [cw1 cw2].
      match type of ev1 with eval _ ?s0 (mkApps ?h _) =>
          assert (csf : closed h) by
            (assert (X : closed s0) by assumption; have := eval_closed Σ HclΣ _ _ X ev1;
             rewrite closedn_mkApps; move/andP => [x1 _]; exact x1) end.
        edestruct R_cunfold_cofix as (fn' & Hfn' & HRfn); [exact Hmf|exact csf|exact cw1|eassumption|].
        clear csf.
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
    - (* proj *)
      match goal with H : with_constructor_as_block = _ |- _ =>
        rewrite <- (cval_app _ _ _ H) in ev1, IHev1 end.
      eapply sim_proj; eassumption.
    - (* proj block *)
      match goal with H : with_constructor_as_block = _ |- _ =>
        rewrite <- (cval_block _ _ _ H) in ev1, IHev1 end.
      eapply sim_proj; eassumption.
    - (* construct *)
      match goal with Hb : with_constructor_as_block = false |- _ => rename Hb into Hblk end.
      have Hbnd : cbound ind c #|args|.
      { intros m i' cd Hl. rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind) in Hl.
        match goal with Hlk : lookup_constructor Σ _ _ = Some _ |- _ => rewrite Hlk in Hl end.
        injection Hl; intros; subst. lia. }
      have Hnf : ~ cfull Σ' ind c #|args|.
      { intros (m & i' & cd & Hl & En).
        rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind) in Hl.
        match goal with Hlk : lookup_constructor Σ _ _ = Some _ |- _ => rewrite Hlk in Hl end.
        injection Hl; intros; subst. lia. }
      eapply app_head; [exact cl| | | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. head_contra ev1. }
      2:{ intros f0' a0' -> Hf D c1' c2' va0'. split_cl cl c1 c2.
          destruct (dead_head_eval Hguard Hprop Σ HclΣ _ _ c1 D ev1)
            as [(? & ? & E)|(? & ? & _ & E & _)]; head_contra E. }
      intros f0' a0' Hf Ha c1' c2'. split_cl cl c1 c2.
      sim_ev ev1 w ee0 Hw; [auto|]. sim_ev ev2 w2 ee2 Hw2; [auto|].
      rewrite -(cval_app _ _ _ Hblk) in Hw.
      destruct (R_construct_unfolds _ _ _ _ Hbnd Hw) as (args' & _ & Hargs & _ & _ & Enf);
        [vof ee0|exact (eval_closed Σ' HclΣ' _ _ c1' ee0)|].
      specialize (Enf Hnf). subst w.
      rewrite !(cval_app _ _ _ Hblk) in Hw. rewrite (cval_app _ _ _ Hblk) in ee0.
      exists (tApp (mkApps (tConstruct ind c []) args') w2). split.
      + sq. eapply eval_construct;
          [ exact Hblk
          | rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind); eassumption
          | exact ee0 | rewrite -(Rs_length _ _ _ Hargs); eassumption | exact ee2].
      + apply R_head; constructor; auto.
    - (* construct block *)
      inversion Ht; subst. cbn in cl.
      match goal with H : Rs _ args _ |- _ =>
        destruct (sim_args _ _ a iha cl _ H) as (args1 & [evs] & Hargs1);
        have Hlen := Rs_length _ _ _ H end.
      eexists. split; [|apply R_head; constructor; eassumption].
      sq. eapply eval_construct_block;
        [eassumption
        | rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind); eassumption
        | rewrite -Hlen; eassumption | exact evs].
    - (* app cong *)
      eapply app_head; [exact cl| | | |exact Ht].
      2:{ intros; subst. apply eval_lambda_inv in ev1. subst. discriminate. }
      2:{ intros f0' a0' -> Hf D c1' c2' va0'. split_cl cl c1 c2. dead_contra D c1 ev1. }
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
      all: try (destruct args; [|discriminate]; inversion Ht; subst;
                match goal with H : Rs _ [] _ |- _ => inversion H; subst end;
                eexists; split; [|apply R_head; exact Ht];
                sq; apply eval_atom; unfold atom;
                rewrite -(ELiftConstants.same_lookup_constructor _ _ Hind); exact i).
      all: inversion Ht; subst.
      all: eexists; split; [sq; apply eval_atom; reflexivity|apply R_head; exact Ht].
  Qed.

  Theorem simulation t v t' :
    eval Σ t v -> closed t -> R Σ' t t' -> goal t' v.
  Proof.
    intros ev cl H. exact (sim_layer _ _ ev (simulation_head _ _ ev cl) _ H).
  Qed.

End Sim.
