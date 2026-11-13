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

Section Typed.
  Context {guard : PCUICWfEnvImpl.abstract_guard_impl}.
  Variables (econf : erasure_configuration) (m : inductives_mapping)
    (p0 : ExAst.global_env * term) (v0 : term).
  Hypothesis Hsat0 : fo_sat (fo_arity (ExAst.trans_env p0.1)) v0.
  Hypothesis Hsat : forall pf, fo_sat (fo_mask_arity (typed_dearg_masks econf m p0 pf)) v0.

  Let q : inductives_mapping * (ExAst.global_env * term) := (m, eta_expand_typed_program p0).
  Let X := pre (typed_analysis_pipeline econf) q.
  Let wv (pf : X) := fo_dearg (typed_dearg_masks econf m p0 pf) v0.
  Let Σd (pf : X) := typed_dearged_env econf m p0 pf.
  Let unb := econf.(enable_unsafe).(unboxing).

  Lemma fo_app_wv pf : fo_app (wv pf).
  Proof. apply fo_dearg_app, Hsat. Qed.

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
    with respect to their declarations (for eta-expansion) and to the
    dearging masks, then [p'] evaluates to [v] with the masked constructor
    arguments dropped. *)
Theorem run_typed_transforms_fo
  econf m lbox (p : ExAst.global_env * term) p' v :
  run_typed_transforms econf m lbox p = ResultMonad.Ok p' ->
  fo_sat (fo_arity (ExAst.trans_env p.1)) v ->
  (forall pf, fo_sat (fo_mask_arity (typed_dearg_masks econf m p pf)) v) ->
  eval_typed_eprogram default_wcbv_flags p v ->
  exists pf,
    eval_typed_eprogram_mapping target_wcbv_flags p'
      (fo_dearg (typed_dearg_masks econf m p pf) v).
Proof.
  intros Hrun H0 Hs ev. unfold run_typed_transforms in Hrun.
  apply with_check_ok in Hrun as [pr ->].
  destruct (fo_eta_typed_lbox_transform_pipeline econf m p v H0 Hs lbox (m, p) pr v ev
              (conj eq_refl eq_refl)) as (v' & ev' & pf & ->).
  exists pf. exact ev'.
Qed.

(** *** Main theorem (typed erasure followed by the untyped passes)

    The expected value is the untyped translation ([fo_value_compile], over
    the dearged environment) of the dearged value.  The correctness of the
    remapping of inductives on the value is assumed, only when a remapping is
    configured. *)
Theorem run_typed_to_untyped_transforms_fo
  econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force
  (p : ExAst.global_env * term) (p' : eprogram) v :
  let unb := econf.(enable_unsafe).(unboxing) in
  run_typed_to_untyped_transforms econf m spec_inst cse lbox lift_consts impl_box
    impl_lazy_force p = ResultMonad.Ok p' ->
  fo_sat (fo_arity (ExAst.trans_env p.1)) v ->
  (forall pf, fo_sat (fo_mask_arity (typed_dearg_masks econf m p pf)) v) ->
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
  intros unb Hrun H0 Hs Hr ev. subst unb. unfold run_typed_to_untyped_transforms in Hrun.
  destruct (remap_on econf).
  - apply join_with_check_ok in Hrun as [pr Hrun].
    destruct (fo_eta_typed_to_untyped_prefix_pipeline econf m p v H0 Hs (m, p) pr v ev
                (conj eq_refl eq_refl)) as (w & evw & pf & ->).
    exists pf.
    eapply remap_then_suffix_fo in Hrun; [exact Hrun| |exact (Hr eq_refl pf)|unfold run, time; exact evw].
    apply fo_unboxed_value_blk, fo_dearg_app, Hs.
  - apply with_check_ok in Hrun as [pr ->].
    destruct (fo_eta_typed_to_untyped_transform_pipeline econf m p v H0 Hs
                spec_inst cse lbox lift_consts impl_box impl_lazy_force (m, p) pr v ev
                (conj eq_refl eq_refl)) as (w & evw & pf & ->).
    exists pf. exact evw.
Qed.
