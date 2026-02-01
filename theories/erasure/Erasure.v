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



Program Definition rebuild_env {fl : EWcbvEval.WcbvFlags} {efl} (with_exp with_fix : bool) :
  Transform.t EEnvMap.GlobalContextMap.t EAst.global_declarations EAst.term EAst.term _ _ (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram_env efl p /\ (with_exp -> preserves_expansion_env with_fix p);
     transform p pre := (EEnvMap.GlobalContextMap.global_decls (fst p), snd p);
     post p := wf_eprogram efl p /\ (with_exp -> preserves_expansion with_fix p);
     obseq p hp p' v v' := v = v' |}.
Next Obligation.
  cbn. unfold preserves_expansion, preserves_expansion_env.
  intros fl efl [] [] input [wf exp]; cbn; split => //.
Qed.
Final Obligation.
  cbn. intros fl efl [] [] input v [] ev p'; exists v; split => //.
Qed.

Program Definition verified_erasure {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t _ _ _ EAst.term _ _
  PCUICTransform.eval_pcuic_program
  (EProgram.eval_eprogram EWcbvEval.default_wcbv_flags) :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform (K _ T1) ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  rebuild_env (efl := efl) true true.
Next Obligation.
  intros guard efl K T1 p.
  cbn. intuition eauto. now eapply H2. now eapply H2.
Qed.
Final Obligation.
  intros guard efl K T1 p. cbn. intuition auto.
Qed.


Program Definition erase_only {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) : Transform.t _ _ _ _ _ _
  eval_template_program
  (EProgram.eval_eprogram EWcbvEval.default_wcbv_flags) :=
  pre_erasure_pipeline ▷
  verified_erasure.
Final Obligation.
  intros guard efl p; cbn. intuition auto.
Qed.

Program Definition run_erase_only p :=
  run erase_only p _.
Final Obligation.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.
