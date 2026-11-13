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
From Peregrine Require Utils CheckWf.
From Peregrine Require Import EInstanceSpecialize.
From Peregrine Require Import ECommonSubexpr.
From Peregrine Require Import ELboxOpts ELboxOptsWf.
From Peregrine Require ELboxOptsSimStatic.
From Peregrine Require Import ELiftConstants.
From Peregrine Require EBetaCorrect.
From Peregrine Require EEtaExpand EEtaExpandSim.
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
     permutation, identity cases, atomic and applied lets), after inlining and
     beta reduction and before boxes are implemented (ELboxOpts.v,
     ELboxOptsWf.v).  The identity-case pass runs first, as its own
     transformation; the other three follow.  Wellformedness and evaluation
     preservation are proved, without axioms (ELboxOptsSim*.v).  Off by
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


(** ** The lambda-box simplifications on typed programs

    Evaluation of a typed program is evaluation of its type-erased program
    ([ExAst.trans_env]), and erasing the types commutes with the
    simplifications ([trans_env_optimize_typed_env]), so the typed passes
    inherit the proofs of the untyped ones ([ELboxOptsSim*], which hold for
    applied constructors and with constructor parameters). Those proofs are
    for unguarded fixpoints, so the typed pipeline first switches to them
    ([typed_unguarded_fix_transform], the identity on programs). *)

Lemma trans_env_optimize_typed_env o Σ :
  ExAst.trans_env (optimize_typed_env o Σ) = optimize_env o (ExAst.trans_env Σ).
Proof.
  unfold ExAst.trans_env, optimize_typed_env, optimize_env. rewrite !map_map.
  apply map_ext. intros [[kn b] d]. cbn. f_equal.
  destruct d as [cb| |[]]; cbn; reflexivity.
Qed.

Definition lbox_opts_typed_program (o : lbox_opts) (p : ExAst.global_env * EAst.term) :
  ExAst.global_env * EAst.term :=
  (optimize_typed_env o p.1, optimize o p.2).

Lemma trans_lbox_opts_typed_program o p :
  (ExAst.trans_env (lbox_opts_typed_program o p).1, (lbox_opts_typed_program o p).2) =
  lbox_opts_program o (ExAst.trans_env p.1, p.2).
Proof. unfold lbox_opts_typed_program, lbox_opts_program. cbn [fst snd]. now rewrite trans_env_optimize_typed_env. Qed.

(** The typed program [staged o optimize_typed_env], in two stages. *)
Lemma staged_typed_env o Σ :
  ExAst.trans_env (staged o optimize_typed_env Σ) = staged o optimize_env (ExAst.trans_env Σ).
Proof.
  unfold staged. destruct lbox_case_id, any_lbox_opts; now rewrite ?trans_env_optimize_typed_env.
Qed.

Program Definition typed_unguarded_fix_transform {fl : EWcbvEval.WcbvFlags}
  {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EWellformed.EEnvFlags}
  (wguard : EWcbvEval.with_guarded_fix) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_mapping fl)
    (eval_typed_eprogram_mapping (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints (typed)";
     transform p _ := p;
     pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
              wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2) /\
              EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.2.1, p.2.2);
     post p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
               wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2);
     obseq p hp p' v v' := v' = v |}.
Next Obligation. cbn. intros. intuition auto. Qed.
Final Obligation.
  cbn. intros fl wcon efl wguard [m [Σ t]] v [_ [wfp [etae etat]]]. cbn in *.
  unfold eval_typed_eprogram_mapping, eval_typed_eprogram. cbn.
  intros [ev]. exists v. split => //. sq.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. 1:auto. 2:apply wfp.
  - now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

(** The passes [o] on a typed program, for any set of rewrites whose node
    rewrite is a chain of steps of the rewrite relation of [ELboxOptsSim].
    With [activate = false] this is the identity ([ETransform.optional_self_transform]
    does not apply to programs with an inductives mapping). *)
Program Definition typed_lbox_opts_transformation {fl : EWcbvEval.WcbvFlags}
  {efl : EWellformed.EEnvFlags} (activate : bool) (o : lbox_opts)
  (hguard : EWcbvEval.with_guarded_fix = false) (hprop : EWcbvEval.with_prop_case = false)
  (hbox : EWellformed.has_tBox)
  (hnode : forall t, ELboxOptsSimStatic.chain t (rewrite_node o t)) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_mapping fl) (eval_typed_eprogram_mapping fl) :=
  {| name := if activate then "lambda-box simplifications (typed)"
             else "skipped lambda-box simplifications (typed)";
     transform p _ := if activate then (p.1, lbox_opts_typed_program o p.2) else p;
     pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
              wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2);
     post p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
               wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2);
     obseq _ _ _ v v' := ELboxOptsSimStatic.obs (wfl := fl) v v' |}.
Next Obligation.
  intros fl efl [] o hguard hprop hbox hnode [m [Σ t]] [wfm wfp]; [|now split].
  cbn -[ExAst.trans_env optimize_typed_env optimize_env] in *.
  rewrite trans_env_optimize_typed_env. split.
  - move: wfm; rewrite /EReorderCstrs.wf_inductives_mapping; solve_all.
    move: H; rewrite /EReorderCstrs.wf_inductive_mapping. destruct x as [ind [na tags]].
    now rewrite lookup_inductive_optimize_env.
  - apply (wf_eprogram_lbox_opts_program o (wellformed_rewrite_node o hbox) (ExAst.trans_env Σ, t) wfp).
Qed.
Final Obligation.
  intros fl efl [] o hguard hprop hbox hnode [m [Σ t]] v [wfm wfp];
    [|intros ev; exists v; split; [exact ev|constructor]].
  unfold eval_typed_eprogram_mapping, eval_typed_eprogram.
  cbn -[ExAst.trans_env optimize_typed_env optimize_env].
  intros ev. rewrite trans_env_optimize_typed_env.
  exact (lbox_opts_program_eval_gen (efl := efl) o hguard hprop hnode (ExAst.trans_env Σ, t) v wfp ev).
Qed.

(** The typed pipeline for the typed backends: [typed_transform_pipeline]
    followed by the lambda-box simplifications selected by [lbox], in the two
    stages of [ELboxOpts.staged]. The result is evaluated with unguarded
    fixpoints; it is not eta-expanded in general (fixpoint eta-hoisting leaves
    fixpoints unapplied), which no typed backend needs. *)
Program Definition typed_lbox_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf (lbox : lbox_opts)
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (eval_typed_eprogram_mapping EWcbvEval.target_wcbv_flags) :=
   typed_transform_pipeline econf ▷
   typed_unguarded_fix_transform (fl := EWcbvEval.opt_wcbv_flags) (wcon := eq_refl) (efl := efl) eq_refl ▷
   typed_lbox_opts_transformation (fl := EWcbvEval.target_wcbv_flags) (efl := efl)
     lbox.(lbox_case_id) case_id_opts eq_refl eq_refl eq_refl ELboxOptsSimStatic.case_id_node ▷
   typed_lbox_opts_transformation (fl := EWcbvEval.target_wcbv_flags) (efl := efl)
     (any_lbox_opts (without_case_id lbox)) (without_case_id lbox) eq_refl eq_refl eq_refl
     (ELboxOptsSimStatic.lbox_node _).
Next Obligation.
  cbn. intros. exact H.
Qed.
Next Obligation.
  cbn. intros. exact H.
Qed.
Final Obligation.
  cbn. intros. exact H.
Qed.

(** What [typed_lbox_transform_pipeline] computes after [typed_transform_pipeline]. *)
Lemma staged_lbox_opts_typed_program o p :
  staged o lbox_opts_typed_program p =
  (staged o optimize_typed_env p.1, staged o optimize p.2).
Proof. unfold staged. destruct p, lbox_case_id, any_lbox_opts; reflexivity. Qed.


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


Import Peregrine.Utils (bool_of_result).
Import Peregrine.CheckWf (check_pipeline_wf, check_pipeline_wf_sound, with_check).

(** * Eta-expansion of the pipeline input

    The pipelines require their input to be eta-expanded
    ([EEtaExpandedFix.expanded_eprogram]). Rocq's erasure produces such
    programs, other frontends in general do not. [EEtaExpand.eta_expand_program]
    establishes the invariant: it is the identity on expanded programs,
    preserves well-formedness and evaluation (up to [EEtaExpandSim.eta_value_rel])
    and always produces an expanded program. *)

Program Definition eta_expand_transform_mapping (efl := nocofix_env_flags) :
  Transform.t _ _ _ _ _ _
    (eval_eprogram_mapping EWcbvEval.default_wcbv_flags)
    (eval_eprogram_mapping EWcbvEval.default_wcbv_flags) :=
  {| name := "eta-expansion of fixpoints and constructors";
     pre p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 /\ wf_eprogram efl p.2;
     transform p hp := (p.1, EEtaExpand.eta_expand_program p.2);
     post p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 /\ wf_eprogram efl p.2 /\
               EEtaExpandedFix.expanded_eprogram p.2;
     obseq p hp p' v v' := EEtaExpandSim.eta_value_rel p.2.1 v v' |}.
Next Obligation.
  intros efl [m p] [hm hwf]. cbn in *. split; [|split].
  - now apply EEtaExpand.wf_inductives_mapping_eta_expand_env.
  - now apply (EEtaExpand.eta_expand_program_wf (efl := efl) eq_refl eq_refl eq_refl eq_refl).
  - now apply (EEtaExpand.eta_expand_program_expanded (efl := efl)).
Qed.
Next Obligation.
  intros efl [m p] v [hm [hwfe hwft]] [ev]. cbn in *.
  destruct (EEtaExpandSim.eta_expand_eval (efl := efl) p.1 p.2 v hwfe
              (EWellformed.wellformed_closed hwft) ev) as (v' & ev' & hv).
  exists v'. split; [exact ev'|exact hv].
Qed.

Program Definition eta_expand_typed_transform_mapping (efl := nocofix_env_flags) :
  Transform.t _ _ _ _ _ _
    (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
    (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags) :=
  {| name := "eta-expansion of fixpoints and constructors (typed)";
     pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
              wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2);
     transform p hp := (p.1, EEtaExpand.eta_expand_typed_program p.2);
     post p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\
               wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2) /\
               EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.2.1, p.2.2);
     obseq p hp p' v v' := EEtaExpandSim.eta_value_rel (ExAst.trans_env p.2.1) v v' |}.
Next Obligation.
  intros efl [m p] [hm hwf]. cbn -[ExAst.trans_env] in *.
  rewrite EEtaExpand.trans_env_eta_expand_ex_env. split; [|split].
  - now apply EEtaExpand.wf_inductives_mapping_eta_expand_env.
  - exact (EEtaExpand.eta_expand_program_wf (efl := efl) eq_refl eq_refl eq_refl eq_refl
             (ExAst.trans_env p.1, p.2) hwf).
  - exact (EEtaExpand.eta_expand_program_expanded (efl := efl) (ExAst.trans_env p.1, p.2) eq_refl hwf).
Qed.
Next Obligation.
  intros efl [m p] v [hm [hwfe hwft]] [ev]. cbn -[ExAst.trans_env] in *.
  destruct (EEtaExpandSim.eta_expand_eval (efl := efl) (ExAst.trans_env p.1) p.2 v hwfe
              (EWellformed.wellformed_closed hwft) ev) as (v' & ev' & hv).
  exists v'. split; [|exact hv].
  unfold eval_typed_eprogram_mapping, eval_typed_eprogram. cbn -[ExAst.trans_env].
  rewrite EEtaExpand.trans_env_eta_expand_ex_env. exact ev'.
Qed.

(** The pipelines on arbitrary well-formed input: eta-expand first. *)

Program Definition eta_untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf spec_inst cse lbox lift_consts impl_box impl_lazy_force
  : Transform.t _ _ _ EAst.term _ _
   (eval_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  eta_expand_transform_mapping ▷
  untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force.
Next Obligation.
  intros guard efl econf spec_inst cse lbox lift_consts impl_box impl_lazy_force p (hm & hwf & hexp).
  exact (conj hm (conj hwf (fun _ => hexp))).
Qed.

Program Definition eta_typed_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (eval_typed_eprogram_mapping EWcbvEval.opt_wcbv_flags) :=
  eta_expand_typed_transform_mapping ▷ typed_transform_pipeline econf.
Next Obligation.
  intros guard efl econf p (hm & hwf & hexp). exact (conj hm (conj hwf hexp)).
Qed.

Program Definition eta_typed_lbox_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf (lbox : lbox_opts)
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (eval_typed_eprogram_mapping EWcbvEval.target_wcbv_flags) :=
  eta_expand_typed_transform_mapping ▷ typed_lbox_transform_pipeline econf lbox.
Next Obligation.
  intros guard efl econf lbox p (hm & hwf & hexp). exact (conj hm (conj hwf hexp)).
Qed.

Program Definition eta_typed_to_untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := nocofix_env_flags) econf spec_inst cse lbox lift_consts impl_box impl_lazy_force
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  eta_expand_typed_transform_mapping ▷
  typed_to_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force.
Next Obligation.
  intros guard efl econf spec_inst cse lbox lift_consts impl_box impl_lazy_force p (hm & hwf & hexp).
  exact (conj hm (conj hwf hexp)).
Qed.

(** * Running the pipelines on checked input

    The remaining precondition (well-formedness of the program and of the
    constructor mapping) is decided by [CheckWf.check_pipeline_wf]; the run
    functions below report an error instead of running the pipeline when the
    input does not satisfy it. *)

Lemma untyped_transform_pipeline_pre econf spec_inst cse lbox lift_consts impl_box impl_lazy_force m p :
  bool_of_result (@check_pipeline_wf nocofix_env_flags m p) = true ->
  pre (eta_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (m, p).
Proof.
  intros h. exact (check_pipeline_wf_sound m p h).
Qed.

Lemma typed_transform_pipeline_pre econf m (p : ExAst.global_env * EAst.term) :
  bool_of_result (@check_pipeline_wf nocofix_env_flags m (ExAst.trans_env p.1, p.2)) = true ->
  pre (eta_typed_transform_pipeline econf) (m, p).
Proof.
  intros h. exact (check_pipeline_wf_sound m _ h).
Qed.

(** The lambda-box stages of [typed_lbox_transform_pipeline] come after
    [typed_transform_pipeline], so after eta-expansion the two have the same
    precondition. *)
Lemma typed_lbox_transform_pipeline_pre econf lbox m (p : ExAst.global_env * EAst.term) :
  bool_of_result (@check_pipeline_wf nocofix_env_flags m (ExAst.trans_env p.1, p.2)) = true ->
  pre (eta_typed_lbox_transform_pipeline econf lbox) (m, p).
Proof.
  intros h. exact (check_pipeline_wf_sound m _ h).
Qed.

Lemma typed_to_untyped_transform_pipeline_pre econf spec_inst cse lbox lift_consts impl_box impl_lazy_force m
  (p : ExAst.global_env * EAst.term) :
  bool_of_result (@check_pipeline_wf nocofix_env_flags m (ExAst.trans_env p.1, p.2)) = true ->
  pre (eta_typed_to_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (m, p).
Proof.
  intros h. exact (check_pipeline_wf_sound m _ h).
Qed.

Definition run_untyped_transforms econf ind_reorder spec_inst cse lbox lift_consts impl_box impl_lazy_force p :=
  with_check (@check_pipeline_wf nocofix_env_flags ind_reorder p)
    (untyped_transform_pipeline_pre econf spec_inst cse lbox lift_consts impl_box impl_lazy_force ind_reorder p)
    (run (eta_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (ind_reorder, p)).

Definition run_typed_transforms econf ind_reorder lbox (p : ExAst.global_env * EAst.term) :=
  with_check (@check_pipeline_wf nocofix_env_flags ind_reorder (ExAst.trans_env p.1, p.2))
    (typed_lbox_transform_pipeline_pre econf lbox ind_reorder p)
    (run (eta_typed_lbox_transform_pipeline econf lbox) (ind_reorder, p)).

Definition run_typed_to_untyped_transforms econf ind_reorder spec_inst cse lbox lift_consts impl_box impl_lazy_force
  (p : ExAst.global_env * EAst.term) :=
  with_check (@check_pipeline_wf nocofix_env_flags ind_reorder (ExAst.trans_env p.1, p.2))
    (typed_to_untyped_transform_pipeline_pre econf spec_inst cse lbox lift_consts impl_box impl_lazy_force ind_reorder p)
    (run (eta_typed_to_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force) (ind_reorder, p)).
