(** * First-order end-to-end correctness of the typed pipelines

    [run_typed_transforms] (typed backends) and
    [run_typed_to_untyped_transforms] (typed erasure followed by the untyped
    passes).  On top of the untyped translation ([EFirstOrderCorrect]) the
    expected value gets a dearging layer: the constructor arguments that the
    dearging analysis found unused are dropped ([fo_dearg]). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed EEnvMap EInlining.
From MetaRocq.Erasure Require EReorderCstrs EImplementBox.
From MetaRocq.Erasure.Typed Require Optimize OptimizeCorrectness ExAst.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ENoCofix ELboxOpts ELboxOptsWf Transforms
  EFirstOrder EFirstOrderStages EFirstOrderPasses EFirstOrderEta ELboxOptsFO
  EEtaExpand EEtaExpandSim EFirstOrderCorrect.
From Peregrine Require ELboxOptsSimStatic.

Import Common.Transform.Transform.

Set Default Goal Selector "!".
#[local] Existing Instance extraction_checker_flags.

(** ** Composition with a postcondition indexed by a parameter fixed by an
    intermediate program *)
Section TripleFam.
  Context {env env' env'' term term' term'' value value' value'' : Type}
    {eval : program env term -> value -> Prop}
    {eval' : program env' term' -> value' -> Prop}
    {eval'' : program env'' term'' -> value'' -> Prop}.

  Lemma fo_triple_compose_fam {X : Type}
    (o : Transform.t env env' term term' value value' eval eval')
    (o' : Transform.t env' env'' term' term'' value' value'' eval' eval'') hpp
    {P : _ -> _ -> Prop} {Q : X -> _ -> _ -> Prop} {R : X -> _ -> _ -> Prop} :
    fo_triple o P (fun p v => exists x, Q x p v) ->
    (forall x, fo_triple o' (Q x) (R x)) ->
    fo_triple (compose o o' hpp) P (fun p v => exists x, R x p v).
  Proof.
    intros H1 H2. eapply fo_triple_compose; [exact H1|].
    intros p pr v ev [x Hx].
    destruct (H2 x p pr v ev Hx) as (v' & ev' & HR).
    exists v'; split; [exact ev'|exists x; exact HR].
  Qed.
End TripleFam.

(** ** Dearging on first-order values *)

(** The number of arguments the dearging masks expect a constructor to be
    applied to. *)
Definition fo_mask_arity (masks : option Optimize.dearg_set) (ind : inductive) (c : nat) : nat :=
  match masks with
  | Some ms => #|Optimize.get_ctor_mask (Optimize.ind_masks ms) ind c|
  | None => 0
  end.

(** The dearging layer of the value translation: [OptimizeCorrectness.dearg_term]
    with the masks of the analysis, the identity when the analysis rejected
    the program. *)
Definition fo_dearg (masks : option Optimize.dearg_set) (v : term) : term :=
  match masks with
  | Some ms => OptimizeCorrectness.dearg_term ms v
  | None => v
  end.

(** On a constructor applied to at least as many arguments as its mask is
    long, dearging drops the masked arguments. *)
Lemma fo_dearg_construct ms ind c args :
  #|Optimize.get_ctor_mask (Optimize.ind_masks ms) ind c| <= #|args| ->
  OptimizeCorrectness.dearg_term ms (mkApps (tConstruct ind c []) args) =
  mkApps (tConstruct ind c [])
    (Optimize.masked (Optimize.get_ctor_mask (Optimize.ind_masks ms) ind c)
       (map (OptimizeCorrectness.dearg_term ms) args)).
Proof.
  intros H. unfold OptimizeCorrectness.dearg_term.
  rewrite OptimizeCorrectness.dearg_mkApps. cbn [Optimize.dearg_aux].
  apply OptimizeCorrectness.dearg_single_masked. now rewrite length_map.
Qed.

Lemma Forall_masked {X} (P : X -> Prop) m xs :
  Forall P xs -> Forall P (Optimize.masked m xs).
Proof.
  induction m as [|[] m IH] in xs |- *; intros H; cbn; auto;
    destruct xs; auto; inversion H; subst; auto.
Qed.

Lemma fo_dearg_app masks v : fo_sat (fo_mask_arity masks) v -> fo_app (fo_dearg masks v).
Proof.
  destruct masks as [ms|]; [|apply fo_sat_app].
  cbn. induction 1 using fo_sat_ind'.
  - cbn. constructor.
  - unfold OptimizeCorrectness.dearg_term, Optimize.dearg.
    destruct p as [? []]; cbn in *; try (now exfalso); constructor; exact H.
  - rewrite fo_dearg_construct; [exact H|].
    constructor. apply Forall_masked. apply Forall_map. exact H1.
Qed.

(** ** The lambda-box simplifications on typed programs *)
Lemma fo_typed_lbox_opts_transformation activate o hnode w :
  fo_app w ->
  fo_triple (typed_lbox_opts_transformation (fl := target_wcbv_flags)
               (efl := nocofix_env_flags) activate o eq_refl eq_refl eq_refl eq_refl hnode)
    (fun _ v => v = w) (fun _ v => v = w).
Proof.
  intros Hw. apply fo_triple_obseq. intros p pr v v' ev HP ev' _. subst v.
  destruct activate.
  - pose proof (correctness (typed_lbox_opts_transformation (fl := target_wcbv_flags)
               (efl := nocofix_env_flags) true o eq_refl eq_refl eq_refl eq_refl hnode) p pr)
      as [_ wf'].
    pose proof pr as [_ wf].
    pose proof (trans_lbox_opts_typed_program o p.2) as E.
    eapply (lbox_opts_program_fo_gen (wfl := target_wcbv_flags) (efl := nocofix_env_flags)
              o eq_refl eq_refl eq_refl eq_refl hnode (ExAst.trans_env p.2.1, p.2.2) w v' wf).
    + rewrite -E. exact wf'.
    + exists w. now apply fo_app_S.
    + exact ev.
    + rewrite -E. exact ev'.
  - destruct ev as [ev], ev' as [ev'].
    exact (eq_sym (eval_deterministic ev ev')).
Qed.

(** ** The analysed program and its masks *)

Definition typed_analysed {guard : PCUICWfEnvImpl.abstract_guard_impl} econf
  (m : inductives_mapping) (p : ExAst.global_env * term)
  (pf : pre (typed_analysis_pipeline econf) (m, eta_expand_typed_program p)) :=
  transform (typed_analysis_pipeline econf) (m, eta_expand_typed_program p) pf.

(** The masks computed by the dearging analysis of the pipeline on the
    (eta-expanded) program; [None] if the analysis rejects it. *)
Definition typed_dearg_masks {guard : PCUICWfEnvImpl.abstract_guard_impl} econf m p pf
  : option Optimize.dearg_set :=
  (typed_analysed econf m p pf).2.1.1.

(** The environment after dearging *)
Definition typed_dearged_env {guard : PCUICWfEnvImpl.abstract_guard_impl} econf m p pf
  : global_declarations :=
  ExAst.trans_env (dearg (typed_analysed econf m p pf).2).1.

(** ** Mask saturation from declaration saturation *)

Lemma forallbi_nth_error {A} (f : nat -> A -> bool) n l i x :
  Optimize.forallbi f n l = true -> nth_error l i = Some x -> f (n + i) x = true.
Proof.
  induction l as [|y l IH] in n, i |- *; cbn; [now destruct i|].
  move/andP=> [Hy Hl]. destruct i as [|i]; cbn.
  - intros [= <-]. now rewrite Nat.add_0_r.
  - intros H. rewrite -Nat.add_succ_comm. now apply IH.
Qed.

Lemma ex_lookup_env_In (Σ : ExAst.global_env) kn d :
  ExAst.lookup_env Σ kn = Some d -> exists b, In (kn, b, d) Σ.
Proof.
  unfold ExAst.lookup_env. induction Σ as [|[[kn' b] d'] Σ IH]; cbn; [discriminate|].
  destruct (eq_kername kn kn') eqn:E.
  - intros [= <-]. apply eqb_eq in E. subst. exists b. now left.
  - intros H. destruct (IH H) as [b' Hin]. exists b'. now right.
Qed.

(** The mask of a declared constructor checked by [valid_masks_env] is as long as
    the constructor's parameters and arguments. *)
Lemma valid_masks_ctor_mask im cm (Σ : ExAst.global_env) ind c np na :
  (forall kn b mib, In (kn, b, ExAst.InductiveDecl mib) Σ ->
     Optimize.valid_masks_decl im cm (kn, b, ExAst.InductiveDecl mib) = true) ->
  lookup_constructor_pars_args (ExAst.trans_env Σ) ind c = Some (np, na) ->
  #|Optimize.get_ctor_mask im ind c| = np + na.
Proof.
  intros Hv. unfold lookup_constructor_pars_args, lookup_constructor, lookup_inductive,
    lookup_minductive.
  rewrite OptimizeCorrectness.lookup_env_trans_env.
  destruct (ExAst.lookup_env Σ (inductive_mind ind)) as [[cst|mib|ta]|] eqn:E; cbn; try discriminate.
  apply ex_lookup_env_In in E as [b Hin]. specialize (Hv _ _ _ Hin). cbn in Hv.
  rewrite nth_error_map.
  destruct (nth_error (ExAst.ind_bodies mib) (inductive_ind ind)) as [oib|] eqn:Eb; cbn; [|discriminate].
  unfold ExAst.trans_ctors. rewrite nth_error_map.
  destruct (nth_error (ExAst.ind_ctors oib) c) as [[[nm ts] nargs]|] eqn:Ec; cbn; [|discriminate].
  intros [= <- <-].
  unfold Optimize.get_ctor_mask.
  destruct (Optimize.get_mib_masks im (inductive_mind ind)) as [mm|]; [|discriminate].
  move/andP: Hv => [Hp Hb]. apply Nat.eqb_eq in Hp.
  rewrite length_app Hp. f_equal.
  pose proof (forallbi_nth_error _ _ _ _ _ Hb Eb) as Ho. cbn in Ho.
  unfold Optimize.check_oib_masks in Ho. move/andP: Ho => [Ho _].
  pose proof (forallbi_nth_error _ _ _ _ _ Ho Ec) as Hc. cbn in Hc.
  now apply eqb_eq in Hc.
Qed.

Lemma valid_masks_env_map_on_snd im cm (g : ExAst.global_decl -> ExAst.global_decl) (Σ : ExAst.global_env) :
  (forall mib, g (ExAst.InductiveDecl mib) = ExAst.InductiveDecl mib) ->
  Optimize.valid_masks_env im cm (map (on_snd g) Σ) = true ->
  forall kn b mib, In (kn, b, ExAst.InductiveDecl mib) Σ ->
     Optimize.valid_masks_decl im cm (kn, b, ExAst.InductiveDecl mib) = true.
Proof.
  intros Hg Hv kn b mib Hin. unfold Optimize.valid_masks_env in Hv.
  rewrite forallb_forall in Hv. rewrite -Hg.
  exact (Hv _ (in_map (on_snd g) _ _ Hin)).
Qed.

(** Saturation with respect to the declarations gives saturation with respect to
    any arity bounded by the declared one, on well-formed values. *)
Lemma fo_sat_weaken {efl : EEnvFlags} {hast : has_tApp} Σ (ar : inductive -> nat -> nat) v :
  (forall ind c np na, lookup_constructor_pars_args Σ ind c = Some (np, na) -> ar ind c <= np + na) ->
  @EWellformed.wellformed efl Σ 0 v -> fo_sat (fo_arity Σ) v -> fo_sat ar v.
Proof.
  intros Har Hwf Hs. revert Hwf.
  induction Hs using fo_sat_ind'; intros Hwf.
  - constructor.
  - now constructor.
  - rewrite (@EWellformed.wellformed_mkApps efl Σ 0 _ args hast) in Hwf. move/andP: Hwf => [Hc Ha]. cbn in Hc.
    move/andP: Hc => [/andP [_ Hl] _].
    unfold fo_arity, lookup_constructor_pars_args in H.
    destruct (lookup_constructor Σ ind c) as [[[mdecl idecl] cdecl]|] eqn:E; [|discriminate].
    cbn in H. constructor.
    + etransitivity; [|exact H]. apply Har. unfold lookup_constructor_pars_args. now rewrite E.
    + clear -H1 Ha.
      induction H1 as [|x l Hx Hl IH]; constructor; cbn in Ha; move/andP: Ha => [Hx' Hl'].
      * now apply Hx.
      * now apply IH.
Qed.

Lemma In_map_on_snd_ind (g : ExAst.global_decl -> ExAst.global_decl) (Σ : ExAst.global_env) kn b mib :
  g (ExAst.InductiveDecl mib) = ExAst.InductiveDecl mib ->
  In (kn, b, ExAst.InductiveDecl mib) Σ -> In (kn, b, ExAst.InductiveDecl mib) (map (on_snd g) Σ).
Proof.
  intros Hg Hin. rewrite -Hg. exact (in_map (on_snd g) _ _ Hin).
Qed.

(** The values of well-formed typed programs are well-formed. *)
Lemma eval_typed_wellformed (p : ExAst.global_env * term) v :
  wf_eprogram nocofix_env_flags (ExAst.trans_env p.1, p.2) ->
  eval_typed_eprogram default_wcbv_flags p v ->
  @wellformed nocofix_env_flags (ExAst.trans_env p.1) 0 v.
Proof.
  intros [Hg Ht] [ev]. exact (eval_wellformed (efl := nocofix_env_flags) _ eq_refl Hg _ _ Ht ev).
Qed.

(** The dearging masks of the analysis are bounded by the declared arities
    ([valid_masks_env], checked by the analysis), so declaration saturation of
    a well-formed value implies mask saturation. *)
Lemma typed_dearg_masks_le {guard : PCUICWfEnvImpl.abstract_guard_impl} econf m p0 pf ind c np na :
  lookup_constructor_pars_args (ExAst.trans_env p0.1) ind c = Some (np, na) ->
  fo_mask_arity (typed_dearg_masks econf m p0 pf) ind c <= np + na.
Proof.
  intros Hl. unfold fo_mask_arity.
  destruct (typed_dearg_masks econf m p0 pf) as [d|] eqn:Ed; [|lia].
  unfold typed_dearg_masks, typed_analysed in Ed. cbn in Ed.
  apply ETransform.check_dearging_precond_spec in Ed as (_ & Hv & _).
  rewrite (valid_masks_ctor_mask (Optimize.ind_masks d) (Optimize.const_masks d) p0.1 ind c np na);
    [|exact Hl|reflexivity].
  intros kn b mib Hin.
  unfold Optimize.valid_masks_env, remove_match_on_box_typed_env, EEtaExpand.eta_expand_ex_env in Hv.
  refine (proj1 (List.forallb_forall _ _) Hv _ _).
  apply In_map_on_snd_ind; [reflexivity|]. apply In_map_on_snd_ind; [reflexivity|]. exact Hin.
Qed.

Lemma typed_dearg_masks_sat {guard : PCUICWfEnvImpl.abstract_guard_impl} econf m p0 v0 pf :
  fo_sat (fo_arity (ExAst.trans_env p0.1)) v0 ->
  @wellformed nocofix_env_flags (ExAst.trans_env p0.1) 0 v0 ->
  fo_sat (fo_mask_arity (typed_dearg_masks econf m p0 pf)) v0.
Proof.
  intros Hs Hwf. eapply (fo_sat_weaken (efl := nocofix_env_flags) (hast := eq_refl)); [|exact Hwf|exact Hs].
  apply typed_dearg_masks_le.
Qed.

Section Typed.
  Context {guard : PCUICWfEnvImpl.abstract_guard_impl}.
  Variables (econf : erasure_configuration) (m : inductives_mapping)
    (p0 : ExAst.global_env * term) (v0 : term).
  Hypothesis Hsat0 : fo_sat (fo_arity (ExAst.trans_env p0.1)) v0.
  Hypothesis Hwf0 : @wellformed nocofix_env_flags (ExAst.trans_env p0.1) 0 v0.

  Let q : inductives_mapping * (ExAst.global_env * term) := (m, eta_expand_typed_program p0).
  Let X := pre (typed_analysis_pipeline econf) q.
  Let wv (pf : X) := fo_dearg (typed_dearg_masks econf m p0 pf) v0.
  Let Σd (pf : X) := typed_dearged_env econf m p0 pf.
  Let unb := econf.(enable_unsafe).(unboxing).

  Lemma fo_app_wv pf : fo_app (wv pf).
  Proof. apply fo_dearg_app, typed_dearg_masks_sat; [exact Hsat0|exact Hwf0]. Qed.

  Lemma fo_eta_expand_typed_transform_mapping :
    fo_triple eta_expand_typed_transform_mapping
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v => p = (m, p0) /\ v = v0)
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v => p = q /\ v = v0).
  Proof.
    apply fo_triple_obseq. intros p pr v v' ev [-> ->] ev' Hobs.
    split; [reflexivity|].
    destruct ev' as [ev']. apply eval_to_value in ev'.
    cbn [transform eta_expand_typed_transform_mapping fst snd eta_expand_typed_program] in ev'.
    rewrite trans_env_eta_expand_ex_env in ev'.
    exact (fo_eta_value_rel _ _ _ Hsat0 Hobs ev').
  Qed.

  Lemma fo_typed_analysis_pipeline :
    fo_triple (typed_analysis_pipeline econf)
      (fun p v => p = q /\ v = v0)
      (fun p v => exists pf : X, p = typed_analysed econf m p0 pf /\ v = v0).
  Proof.
    intros p pr v ev [-> ->].
    destruct (preservation (typed_analysis_pipeline econf) q v0 pr ev) as (v' & ev' & Hobs).
    exists v'. split; [exact ev'|]. exists pr. split; [reflexivity|].
    cbn in Hobs. destruct Hobs as (v1 & H1 & H2). subst.
    apply fo_remove_match_on_box. exact (fo_sat_app _ _ Hsat0).
  Qed.

  Lemma fo_dearging_transform_mapping (pf : X) :
    fo_triple (dearging_transform_mapping econf.(dearging_config))
      (fun p v => p = typed_analysed econf m p0 pf /\ v = v0)
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v =>
         p.1 = m /\ ExAst.trans_env p.2.1 = Σd pf /\ v = wv pf).
  Proof.
    apply fo_triple_obseq. intros p pr v v' ev [-> ->] ev' Hobs.
    change (v' = (dearg ((typed_analysed econf m p0 pf).2.1, v0)).2) in Hobs.
    subst v'. split; [reflexivity|]. split; [reflexivity|].
    unfold wv, fo_dearg, typed_dearg_masks, dearg. cbn [fst snd].
    destruct ((typed_analysed econf m p0 pf).2.1.1); reflexivity.
  Qed.

  (** *** The typed pipeline with the lambda-box passes *)
  Lemma fo_eta_typed_lbox_transform_pipeline lbox :
    fo_triple (eta_typed_lbox_transform_pipeline econf lbox)
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v => p = (m, p0) /\ v = v0)
      (fun _ v => exists pf : X, v = wv pf).
  Proof.
    unfold eta_typed_lbox_transform_pipeline.
    eapply fo_triple_compose; [apply fo_eta_expand_typed_transform_mapping|].
    unfold typed_lbox_transform_pipeline.
    eapply (fo_triple_compose_fam _ _ _ (Q := fun (pf : X) _ v => v = wv pf));
      [|intros pf; apply fo_typed_lbox_opts_transformation, fo_app_wv].
    eapply (fo_triple_compose_fam _ _ _ (Q := fun (pf : X) _ v => v = wv pf));
      [|intros pf; apply fo_typed_lbox_opts_transformation, fo_app_wv].
    eapply (fo_triple_compose_fam _ _ _ (Q := fun (pf : X) _ v => v = wv pf));
      [|intros pf; apply fo_typed_lbox_opts_transformation, fo_app_wv].
    eapply (fo_triple_compose_fam _ _ _ (Q := fun (pf : X) _ v => v = wv pf));
      [|intros pf; apply fo_triple_obseq; intros p pr v v' ev -> ev' Hobs; exact Hobs].
    unfold typed_transform_pipeline.
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) p v => p = typed_analysed econf m p0 pf /\ v = v0)).
    - apply fo_typed_analysis_pipeline.
    - intros pf. eapply fo_triple_conseq; [| |apply (fo_dearging_transform_mapping pf)].
      + intros ? ? H; exact H.
      + cbn. intros ? ? (_ & _ & H); exact H.
  Qed.

  (** *** Typed erasure followed by the untyped passes *)
  Lemma fo_typed_to_untyped_prefix_pipeline :
    fo_triple (typed_to_untyped_prefix_pipeline econf)
      (fun p v => p = q /\ v = v0)
      (fun _ v => exists pf : X, v = fo_unboxed_value m (Σd pf) unb (wv pf)).
  Proof.
    unfold typed_to_untyped_prefix_pipeline.
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) (p : eprogram) v =>
                      (forall ind c, fo_unboxable p.1 ind c =
                         fo_unboxable (EReorderCstrs.reorder_env m (Σd pf)) ind c) /\
                      v = fo_blocks_value m (Σd pf) (wv pf)));
      [|intros pf; apply fo_nocofix_unboxing_transforms, fo_app_wv].
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) (p : inductives_mapping * eprogram_env) v =>
                      p.1 = m /\ (p.2.1 : global_declarations) = Σd pf /\ v = wv pf));
      [|intros pf; apply fo_nocofix_lambdabox_typed_pipeline, fo_app_wv].
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) (p : inductives_mapping * eprogram) v =>
                      p.1 = m /\ p.2.1 = Σd pf /\ v = wv pf));
      [|intros pf; apply fo_triple_obseq; intros p pr v v' ev HP ev' Hobs;
        cbn in *; subst; exact HP].
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) (p : inductives_mapping * (ExAst.global_env * term)) v =>
                      p.1 = m /\ ExAst.trans_env p.2.1 = Σd pf /\ v = wv pf));
      [|intros pf; apply fo_triple_obseq; intros p pr v v' ev HP ev' Hobs;
        cbn -[ExAst.trans_env] in *; subst; exact HP].
    unfold typed_transform_pipeline.
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) p v => p = typed_analysed econf m p0 pf /\ v = v0)).
    - apply fo_typed_analysis_pipeline.
    - intros pf. apply fo_dearging_transform_mapping.
  Qed.

  Lemma fo_eta_typed_to_untyped_prefix_pipeline :
    fo_triple (eta_typed_to_untyped_prefix_pipeline econf)
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v => p = (m, p0) /\ v = v0)
      (fun _ v => exists pf : X, v = fo_unboxed_value m (Σd pf) unb (wv pf)).
  Proof.
    unfold eta_typed_to_untyped_prefix_pipeline.
    eapply fo_triple_compose; [apply fo_eta_expand_typed_transform_mapping|].
    apply fo_typed_to_untyped_prefix_pipeline.
  Qed.

  Lemma fo_eta_typed_to_untyped_transform_pipeline
    spec_inst cse lbox lift_consts impl_box impl_lazy_force :
    fo_triple (eta_typed_to_untyped_transform_pipeline econf
                 spec_inst cse lbox lift_consts impl_box impl_lazy_force)
      (fun (p : inductives_mapping * (ExAst.global_env * term)) v => p = (m, p0) /\ v = v0)
      (fun _ v => exists pf : X, v = fo_value_compile m (Σd pf) unb impl_box (wv pf)).
  Proof.
    unfold eta_typed_to_untyped_transform_pipeline.
    eapply fo_triple_compose; [apply fo_eta_expand_typed_transform_mapping|].
    unfold typed_to_untyped_transform_pipeline.
    eapply (fo_triple_compose_fam _ _ _
              (Q := fun (pf : X) (_ : eprogram) v => v = fo_unboxed_value m (Σd pf) unb (wv pf))).
    - apply fo_typed_to_untyped_prefix_pipeline.
    - intros pf. apply fo_untyped_suffix_pipeline, fo_unboxed_value_blk, fo_app_wv.
  Qed.
End Typed.

(** ** The pipelines as run by Peregrine *)

(** *** Main theorem (typed backends)

    If [run_typed_transforms] succeeds with [p'] and the source program
    evaluates to a first-order value [v] whose constructors are saturated
    with respect to their declarations, then [p'] evaluates to [v] with the
    masked constructor arguments dropped.  (Saturation with respect to the
    dearging masks follows, see [typed_dearg_masks_sat].)  The dearging
    configuration is the one [run_typed_transforms] adapts to the
    eta-expanded program ([eta_econf]). *)
Theorem run_typed_transforms_fo {guard : PCUICWfEnvImpl.abstract_guard_impl}
  econf0 m lbox (p : ExAst.global_env * term) p' v :
  let econf := eta_econf econf0 p.1 in
  run_typed_transforms econf0 m lbox p = ResultMonad.Ok p' ->
  fo_sat (fo_arity (ExAst.trans_env p.1)) v ->
  eval_typed_eprogram default_wcbv_flags p v ->
  exists pf,
    eval_typed_eprogram_mapping target_wcbv_flags p'
      (fo_dearg (typed_dearg_masks econf m p pf) v).
Proof.
  intros econf Hrun H0 ev. unfold run_typed_transforms in Hrun.
  cbv zeta in Hrun. change (eta_econf econf0 p.1) with econf in Hrun.
  apply with_check_ok in Hrun as [pr ->].
  pose proof (eval_typed_wellformed p v (proj2 pr) ev) as Hwf.
  destruct (fo_eta_typed_lbox_transform_pipeline econf m p v H0 Hwf lbox (m, p) pr v ev
              (conj eq_refl eq_refl)) as (v' & ev' & pf & ->).
  exists pf. exact ev'.
Qed.

(** *** Main theorem (typed erasure followed by the untyped passes)

    The expected value is the untyped translation ([fo_value_compile], over
    the dearged environment) of the dearged value.  The correctness of the
    remapping of inductives on the value is assumed, only when a remapping is
    configured.  As in [run_typed_transforms_fo], the dearging configuration
    is the one adapted to the eta-expanded program ([eta_econf]). *)
Theorem run_typed_to_untyped_transforms_fo {guard : PCUICWfEnvImpl.abstract_guard_impl}
  econf0 m spec_inst cse lbox lift_consts impl_box impl_lazy_force
  (p : ExAst.global_env * term) (p' : eprogram) v :
  let econf := eta_econf econf0 p.1 in
  let unb := econf.(enable_unsafe).(unboxing) in
  run_typed_to_untyped_transforms econf0 m spec_inst cse lbox lift_consts impl_box
    impl_lazy_force p = ResultMonad.Ok p' ->
  fo_sat (fo_arity (ExAst.trans_env p.1)) v ->
  (remap_on econf = true ->
   forall pf, remap_fo econf
                (fo_unboxed_value m (typed_dearged_env econf m p pf) unb
                   (fo_dearg (typed_dearg_masks econf m p pf) v))) ->
  eval_typed_eprogram default_wcbv_flags p v ->
  exists pf,
    eval_eprogram final_wcbv_flags p'
      (fo_value_compile m (typed_dearged_env econf m p pf) unb impl_box
         (fo_dearg (typed_dearg_masks econf m p pf) v)).
Proof.
  intros econf unb Hrun H0 Hr ev. subst unb. unfold run_typed_to_untyped_transforms in Hrun.
  cbv zeta in Hrun. change (eta_econf econf0 p.1) with econf in Hrun.
  destruct (remap_on econf).
  - apply join_with_check_ok in Hrun as [pr Hrun].
    pose proof (eval_typed_wellformed p v (proj2 pr) ev) as Hwf.
    destruct (fo_eta_typed_to_untyped_prefix_pipeline econf m p v H0 Hwf (m, p) pr v ev
                (conj eq_refl eq_refl)) as (w & evw & pf & ->).
    exists pf.
    eapply remap_then_suffix_fo in Hrun; [exact Hrun| |exact (Hr eq_refl pf)|unfold run, time; exact evw].
    apply fo_unboxed_value_blk, fo_dearg_app, typed_dearg_masks_sat; [exact H0|exact Hwf].
  - apply with_check_ok in Hrun as [pr ->].
    pose proof (eval_typed_wellformed p v (proj2 pr) ev) as Hwf.
    destruct (fo_eta_typed_to_untyped_transform_pipeline econf m p v H0 Hwf
                spec_inst cse lbox lift_consts impl_box impl_lazy_force (m, p) pr v ev
                (conj eq_refl eq_refl)) as (w & evw & pf & ->).
    exists pf. exact evw.
Qed.
