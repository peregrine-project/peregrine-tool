From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Template Require Import EtaExpand TemplateProgram.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaRocq.Erasure Require Import EProgram EInlining EBeta EWellformed.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From MetaRocq.Erasure Require EImplementBox.
From MetaRocq.Erasure Require EImplementLazyForce ERemapInductives.
From Peregrine Require Import EExtraFlags ENoCofix.
From Peregrine Require Import EInstanceSpecialize.
From Peregrine Require Import ECommonSubexpr.
From Peregrine Require Import ELboxOpts ELboxOptsWf.
From Peregrine Require Import ELiftConstants.
From Peregrine Require EBetaCorrect.
From Malfunction Require Pipeline.

Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Common.Transform.Transform.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Local Obligation Tactic := idtac.



Program Definition implement_box_transformation
  (efl := extra_env_flags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram EImplementBox.block_wcbv_flags) (eval_eprogram EImplementBox.block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (EImplementBox.switch_off_box efl) p ;
    obseq p hp p' v v' := v' = EImplementBox.implement_box v |}.
Next Obligation.
  intros. cbn in *.
  split.
  - eapply EImplementBox.implement_box_env_wf_glob; eauto. apply p.
  - eapply EImplementBox.transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Final Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply EImplementBox.implement_box_eval; cbn; eauto.
  all: try reflexivity.
Qed.

Program Definition implement_lazy_force_transformation
  (efl := extra_env_flags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram final_wcbv_flags) (eval_eprogram final_wcbv_flags) :=
  {| name := "implementing lazy/force";
    transform p _ := EImplementLazyForce.implement_lazy_force_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (EImplementLazyForce.switch_off_thunk efl) p ;
    obseq p hp p' v v' := v' = EImplementLazyForce.implement_lazy_force v |}.
Next Obligation.
  intros. cbn in *.
  split.
  - eapply EImplementLazyForce.implement_lazy_force_env_wf_glob; eauto. apply p.
  - eapply EImplementLazyForce.transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Final Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply EImplementLazyForce.implement_lazy_force_eval; cbn; eauto.
  all: try reflexivity.
Qed.

Definition switch_off_box_wf env t l :
  let efl := extra_env_flags in
  wellformed (EImplementBox.switch_off_box efl) env l t ->
  wellformed efl env l t.
Proof.
  cbn.
  generalize dependent l.
  induction t using EInduction.term_forall_list_ind; auto; try discriminate; intro l'; try (simpl; rtoProp; solve_all).
  - unfold wf_fix in *.
    rtoProp.
    solve_all.
  - inversion X; auto; subst.
    destruct X0.
    cbn in *. unfold EPrimitive.test_array_model in *.
    rtoProp. solve_all.
Qed.

Definition switch_off_box_wf_glob env :
  let efl := extra_env_flags in
  wf_glob (EImplementBox.switch_off_box efl) env ->
  wf_glob efl env.
Proof.
  cbn.
  induction env.
  - constructor.
  - destruct a. cbn.
    intros.
    inversion H; subst.
    constructor; auto.
    destruct g.
    + destruct c, cst_body0; auto.
      apply switch_off_box_wf. assumption.
    + cbn.
      assumption.
Qed.

Definition switch_off_box_wf_eprogram p :
  let efl := extra_env_flags in
  wf_eprogram (EImplementBox.switch_off_box efl) p ->
  wf_eprogram efl p.
Proof.
  intros.
  destruct H.
  split.
  - apply switch_off_box_wf_glob.
    assumption.
  - apply switch_off_box_wf.
    assumption.
Qed.


Program Definition extra_unsafe_transforms (spec_inst cse : bool) (lbox : lbox_opts) (lift_consts impl_box impl_lazy_force : bool) :=
  let efl := extra_env_flags in
  (* Instance/dictionary specialization, then common-subexpression
     elimination, both in the constructors-as-blocks regime of [implement_box].
     They run after [optional_unsafe_transforms], so betared and dead-argument
     elimination do not see their output, then the lifting of closed
     constructor values to shared constants.  All three are off by default.
     The semantic obligations of the specialization and of the lifting are
     proved (EInstanceSpecialize.v with ESpecRel.v; ELiftConstants.v); those
     of the CSE rest on axioms (ECommonSubexpr.v). *)
  ETransform.optional_self_transform spec_inst
    specialize_instances_transformation ▷
  ETransform.optional_self_transform cse
    (cse_transformation efl EImplementBox.block_wcbv_flags) ▷
  (* Lambda-box simplifications (fixpoint eta-hoisting, case/function
     permutation, identity cases, let/function permutation), after inlining and
     beta reduction and before boxes are implemented (ELboxOpts.v,
     ELboxOptsWf.v).  The identity-case pass runs first, as its own
     transformation; the other three follow.  Wellformedness and evaluation
     preservation are proved, except that with fixpoint eta-hoisting enabled
     only termination is assumed (axiom trust_fix_eta_terminates).  Off by
     default. *)
  ETransform.optional_self_transform lbox.(lbox_case_id)
    case_id_transformation ▷
  ETransform.optional_self_transform (any_lbox_opts (without_case_id lbox))
    (lbox_opts_transformation lbox) ▷
  (* Lifting of closed constructor values (nat literals, ...) to shared global
     constants (ELiftConstants.v; proved, lift_program_wf /
     lift_program_pres).  Last of the simplifications, so that it sees
     the simplified terms, and before boxes are implemented.  Off by default. *)
  ETransform.optional_self_transform lift_consts
    (lift_constants_transformation efl EImplementBox.block_wcbv_flags) ▷
  ETransform.optional_self_transform impl_box implement_box_transformation ▷
  ETransform.optional_self_transform impl_lazy_force implement_lazy_force_transformation.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, (lbox_case_id lbox), (any_lbox_opts (without_case_id lbox)), lift_consts, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.


(** * The verified λ□ pipelines and MetaRocq's optional passes, without cofixpoints

    Copies of MetaRocq's [verified_lambdabox_pipeline],
    [verified_lambdabox_pipeline_mapping] and [verified_lambdabox_typed_pipeline]
    (ErasurePlugin/Erasure.v), instantiated at [nocofix_env_flags] instead of
    [all_env_flags]: [check_wf] (Pipeline.v) rejects cofixpoints, and the
    absence of cofixpoints is carried to [extra_unsafe_transforms], where the
    implementation of boxes and of lazy/force needs it.  The passes are
    MetaRocq's and generic in the flags; only the flags differ. *)

#[local] Obligation Tactic := program_simpl.

Program Definition nocofix_lambdabox_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf
  : Transform.t _ _ _ EAst.term _ _
   (eval_eprogram_env EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  guarded_to_unguarded_fix (fl := EWcbvEval.default_wcbv_flags) (wcon := eq_refl) eq_refl ▷
  remove_params_optimization (wcon := eq_refl) efl eq_refl eq_refl ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params efl) true false ▷
  remove_match_on_box_trans (efl := ERemoveParams.switch_no_params efl) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params efl) true false ▷
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (efl := ERemoveParams.switch_no_params efl)
    (wcon := eq_refl) eq_refl eq_refl (has_app := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params efl)) true false ▷
  constructors_as_blocks_transformation
    (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params efl))
    (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl) ▷
  ETransform.optional_self_transform econf.(inlining) (inlining_transformation (efl := efl) eq_refl econf).
Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs.
Qed.
Next Obligation.
  now destruct econf as [? ? ? [] ?].
Qed.

Program Definition nocofix_lambdabox_pipeline_mapping {guard : abstract_guard_impl} econf
  (efl := nocofix_env_flags)
  : Transform.t _ _ _ EAst.term _ _
   (eval_eprogram_env_mapping EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  reorder_cstrs_transformation (wca := eq_refl) (has_app := eq_refl) EWcbvEval.default_wcbv_flags (wcon := eq_refl) ▷
  rebuild_wf_env_transform (efl := efl) true true ▷
  nocofix_lambdabox_pipeline econf.

Program Definition nocofix_lambdabox_typed_pipeline (efl := nocofix_env_flags)
  (wfl := {| EWcbvEval.with_prop_case := false; EWcbvEval.with_guarded_fix := true; EWcbvEval.with_constructor_as_block := false |}) econf :
  Transform.t _ _ _ EAst.term _ _
    (eval_eprogram_env_mapping wfl)
    (EProgram.eval_eprogram final_wcbv_flags) :=
  reorder_cstrs_transformation (wca := eq_refl) (has_app := eq_refl) wfl (wcon := eq_refl) ▷
  rebuild_wf_env_transform (efl := efl) true true ▷
  guarded_to_unguarded_fix (fl := {| EWcbvEval.with_prop_case := false; EWcbvEval.with_guarded_fix := true; EWcbvEval.with_constructor_as_block := false |}) (wcon := eq_refl) eq_refl ▷
  remove_params_optimization (wcon := eq_refl) efl eq_refl eq_refl ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params efl) true false ▷
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (efl := ERemoveParams.switch_no_params efl)
    (wcon := eq_refl) eq_refl eq_refl (has_app := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params efl)) true false ▷
  constructors_as_blocks_transformation
    (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params efl))
    (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl) ▷
  ETransform.optional_self_transform econf.(inlining) (inlining_transformation (efl := efl) eq_refl econf).
Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs.
Qed.
Next Obligation.
  destruct econf as [? ? ? []]=> //.
Qed.

(** MetaRocq's [optional_unsafe_transforms] without the translation of
    cofixpoints to lazy fixpoints ([cofix_to_lazy], whose correctness is the
    false axiom [ECoInductiveToInductive.trust_cofix]).  Unboxing, which
    MetaRocq runs only after that translation because it needs the absence of
    cofixpoints, runs whenever it is enabled: the flags here exclude
    cofixpoints.  The [cofix_to_lazy] field of the configuration is ignored.
    Beta-reduction is [EBeta.betared_program] with the proved
    [EBetaCorrect.betared_transformation] in place of MetaRocq's
    [EBeta.betared_transformation], whose obligations are axioms. *)
Program Definition nocofix_unsafe_transforms econf :=
  let passes := econf.(enable_unsafe) in
  let efl := extra_env_flags in
  ETransform.optional_self_transform passes.(unboxing)
    (rebuild_wf_env_transform (efl := efl) false false ▷
     unbox_transformation efl final_wcbv_flags (has_app := eq_refl) (has_cofix := eq_refl)
       (has_prop_case := eq_refl) (has_letin := eq_refl) (has_cstrparams := eq_refl) (has_cstr_block := eq_refl)) ▷
  ETransform.optional_self_transform passes.(inductives_extraction)
    (rebuild_wf_env_transform (efl := efl) false false ▷
       ERemapInductives.extract_inductive_transformation efl final_wcbv_flags econf.(extracted_inductives) ▷
       ERemapInductives.forget_inductive_extraction_info_transformation efl final_wcbv_flags) ▷
  (* Heuristically do it twice for more beta-normal terms *)
  ETransform.optional_self_transform passes.(betared)
    (EBetaCorrect.betared_transformation efl (hasapp := eq_refl) ▷
     EBetaCorrect.betared_transformation efl (hasapp := eq_refl)).
Next Obligation.
  destruct (enable_unsafe econf) as [? [] [] []]; cbn in * => //; intuition auto.
Qed.
Next Obligation.
  destruct (enable_unsafe econf) as [? [] [] []]; cbn in * => //; intuition auto.
Qed.

#[local] Obligation Tactic := idtac.


Program Definition untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf spec_inst cse lbox lift_consts impl_box impl_lazy_force
  : Transform.t _ _ _ EAst.term _ _
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (eval_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (* Target evaluation, with no more cases on prop, unguarded fixpoints, constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  rebuild_wf_env_transform_mapping true true ▷
  nocofix_lambdabox_pipeline_mapping econf ▷
  nocofix_unsafe_transforms econf ▷
  extra_unsafe_transforms spec_inst cse lbox lift_consts impl_box impl_lazy_force.
Next Obligation.
  cbn. intros.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  cbn. intros.
  destruct econf as [[? [] ? ?] ? ? [] ? ?]; cbn in *; intuition auto.
Qed.
Final Obligation.
  cbn. intros.
  destruct econf as [[? ? ? []] ? ? ? ? ?], spec_inst; cbn in *; auto.
Qed.


Section Dearging.
  Import Optimize OptimizeCorrectness.

  Definition dearg (p : (option dearg_set × ExAst.global_env) * EAst.term) : ExAst.global_env * EAst.term :=
    match p.1.1 with
    | Some masks => ((dearg_env masks p.1.2), dearg_term masks p.2)
    | None => (p.1.2, p.2)
    end.

  Program Definition dearging_transform (efl := nocofix_env_flags) cf :
    Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram_masks EWcbvEval.opt_wcbv_flags) (eval_typed_eprogram EWcbvEval.opt_wcbv_flags) :=
    {| name := "dearging";
      transform p _ := dearg p ;
      pre p := post_dearging_checks efl cf p;
      post p := wf_eprogram efl (ExAst.trans_env p.1, p.2) /\ EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.1, p.2) ;
      obseq p hp p' v v' := v' = (dearg (p.1, v)).2 |}.
  Next Obligation.
  Proof.
    cbn. intros.
    unfold dearg.
    destruct p. rewrite H.
    destruct check_dearging_precond eqn:eqp; cbn -[ExAst.trans_env] => //.
    destruct input as [[masks env] t]. cbn -[ExAst.trans_env Optimize.dearg_env] in *.
    subst masks. destruct H0 as [wf exp].
    (* Wellformedness at [nocofix_env_flags] is wellformedness at
       [all_env_flags], where MetaRocq proves dearging correct, and the
       absence of cofixpoints, which dearging preserves (ENoCofix.v). *)
    apply wf_eprogram_nocofix in wf as [wf [gnc tnc]].
    eapply check_dearging_precond_spec in eqp. intuition.
    - apply wf_eprogram_nocofix; cbn -[ExAst.trans_env]. split; [|split].
      + split; cbn.
        unfold dearg_env.
        eapply wf_glob_debox.
        eapply wf_glob_dearg; eauto.
        eapply wf.
        rewrite /dearg_env. rewrite -trans_env_debox.
        eapply wellformed_dearg; eauto.
        eapply wf.
      + now apply glob_no_cofix_dearg_env'.
      + now apply no_cofix_dearg.
    - rewrite /dearg_env -trans_env_debox. split; cbn.
      eapply expanded_dearg_env; tea. apply exp.
      eapply EEtaExpandedFix.isEtaExp_expanded, expanded_dearg; eauto.
      apply EEtaExpandedFix.expanded_isEtaExp, exp.
  Qed.
  Final Obligation.
    cbn. intros. red.
    intros p v [he [wfe exp]]. unfold eval_typed_eprogram_masks.
    intros [ev].
    unfold dearg. rewrite he.
    destruct (check_dearging_precond) as [masks|] eqn:cpre.
    * eapply (ExtractionCorrectness.extract_correct_gen' _ _ _ masks cf.(overridden_masks) cf.(do_trim_const_masks) cf.(do_trim_ctor_masks)) in ev as ev'.
      destruct ev' as [ev'].
      eexists. split. red. sq. cbn. exact ev'. auto.
      - destruct wfe. now eapply EWellformed.wellformed_closed_env.
      - destruct wfe. now eapply EWellformed.wellformed_closed.
      - move: cpre. unfold check_dearging_precond. destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct (_ && _) => //. congruence.
      - move: cpre. rewrite /check_dearging_precond.
        destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded => //. now intros [= ->].
      - move: cpre. rewrite /check_dearging_precond.
        destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded eqn:ise => //. now intros [= ->].
    * exists v. cbn. split => //.
  Qed.
End Dearging.

Program Definition dearging_transform_mapping (cf : ETransform.dearging_config) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_masks_mapping EWcbvEval.opt_wcbv_flags) (eval_typed_eprogram_mapping EWcbvEval.opt_wcbv_flags)  :=
  let tr := (dearging_transform cf) in
 {| name := name tr;
    pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1.2) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  cbn.
  split => //.
  2:{ now unshelve eapply (correctness (dearging_transform cf)). }
  destruct p.
  move: H; rewrite /EReorderCstrs.wf_inductives_mapping; solve_all.
  move: H; rewrite /EReorderCstrs.wf_inductive_mapping. destruct x as [ind [na tags]].
  rewrite /dearg. destruct input.2.1.1 => //.
  rewrite /OptimizeCorrectness.dearg_env.
  rewrite /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive /=.
  rewrite !OptimizeCorrectness.lookup_env_trans_env.
  rewrite OptimizeCorrectness.lookup_env_debox_env_types option_map_two /=.
  rewrite OptimizeCorrectness.lookup_env_dearg_env option_map_two /=.
  destruct ExAst.lookup_env => //=; destruct g => //=.
  rewrite !nth_error_map option_map_two /=.
  rewrite /Optimize.dearg_mib /=. destruct Optimize.get_mib_masks => //=.
  rewrite !nth_error_mapi.
  1-2:destruct nth_error eqn:hnth => //=; len.
  intros _. destruct o => //=. destruct p => //.
Qed.
Final Obligation.
Proof.
  intros cf p v pr ev. cbn.
  now unshelve eapply (preservation (dearging_transform cf)).
Qed.

Program Definition typed_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (eval_typed_eprogram_mapping EWcbvEval.opt_wcbv_flags) :=

   remove_match_on_box_typed_transform_mapping (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl)
    (fl := EWcbvEval.default_wcbv_flags) ▷
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   dearging_checks_transform_mapping econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   dearging_transform_mapping econf.(dearging_config).
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  intros. cbn.
  apply H.
Qed.
Final Obligation.
  cbn. intros.
  apply H.
Qed.




Program Definition trans_env_transform {fl : EWcbvEval.WcbvFlags} {efl : EWellformed.EEnvFlags} :
  Transform.t _ _  _ _ _ _ (eval_typed_eprogram_mapping fl) (eval_eprogram_mapping fl) :=
  {| name := "typed to untyped transform";
    pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2) /\ EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.2.1, p.2.2);
    transform p hp := (p.1, (ExAst.trans_env p.2.1, p.2.2)) ;
    post p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 /\ wf_eprogram efl p.2 /\ EEtaExpandedFix.expanded_eprogram p.2 ;
    obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros ? ? ? H.
  cbn in *.
  move: H; rewrite /EReorderCstrs.wf_inductives_mapping; solve_all.
Qed.
Final Obligation.
  intros ? ? ? ? ? ?.
  unfold eval_typed_eprogram_mapping, eval_typed_eprogram in H.
  exists v.
  unfold eval_eprogram_mapping, eval_eprogram.
  cbn.
  split; auto.
Qed.


Program Definition typed_to_untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf spec_inst cse lbox lift_consts impl_box impl_lazy_force
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=

   typed_transform_pipeline econf ▷
   trans_env_transform ▷
   rebuild_wf_env_transform_mapping true true ▷
   nocofix_lambdabox_typed_pipeline econf ▷
   nocofix_unsafe_transforms econf ▷
   extra_unsafe_transforms spec_inst cse lbox lift_consts impl_box impl_lazy_force.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  cbn. intros.
  destruct econf as [[? [] ? ?] ? ? [] ? ?]; cbn in *; intuition auto.
Qed.
Final Obligation.
  cbn. intros.
  destruct econf as [[? ? ? []] ? ? ? ? ?], spec_inst; cbn in *; auto.
Qed.


Program Definition run_untyped_transforms econf ind_reorder spec_inst cse lbox lift_consts impl_box impl_lazy_force p :=
  run (untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)

Program Definition run_typed_transforms econf ind_reorder p :=
  run (typed_transform_pipeline econf) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)

Program Definition run_typed_to_untyped_transforms econf ind_reorder spec_inst cse lbox lift_consts impl_box impl_lazy_force p :=
  run (typed_to_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)
