From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Template Require Import EtaExpand TemplateProgram.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaRocq.Erasure Require Import EProgram EInlining EBeta.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.

Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Common.Transform.Transform.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Local Obligation Tactic := idtac.



Program Definition verified_typed_erasure {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  Transform.t _ _ _ _ _ _
   PCUICTransform.eval_pcuic_program
   (eval_typed_eprogram EWcbvEval.default_wcbv_flags) :=
   (* a bunch of nonsense for normalization preconditions *)
   let K ty (T : ty -> _) p
     := let p := T p in
        (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
          (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
   let T1 (p:global_env_ext_map) := p in
   (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
   pcuic_expand_lets_transform (K _ T1) ▷
   (* Erasure of proofs terms in Prop and types *)
   typed_erase_transform.
  Final Obligation.
    cbn. intros. assumption.
  Qed.


Program Definition typed_erase_only {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) : Transform.t _ _ _ _ _ _
  eval_template_program
  (eval_typed_eprogram EWcbvEval.default_wcbv_flags) :=
  pre_erasure_pipeline ▷
  verified_typed_erasure.
Final Obligation.
  intros guard efl p; cbn. intuition auto.
Qed.

Program Definition run_typed_erase_only p :=
  run typed_erase_only p _.
Final Obligation.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.
