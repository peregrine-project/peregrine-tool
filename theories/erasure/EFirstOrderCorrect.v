(** * First-order end-to-end correctness of the λ□ middle end *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed EEnvMap EInlining.
From MetaRocq.Erasure Require EReorderCstrs ERemoveParams EOptimizePropDiscr
  EInlineProjections EConstructorsAsBlocks EUnboxing EImplementBox EImplementLazyForce.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ENoCofix ESpecRel EInstanceSpecialize
  ECommonSubexpr ELboxOpts ELboxOptsWf ELiftConstants EBetaCorrect Transforms
  EFirstOrder EFirstOrderStages EFirstOrderPasses EFirstOrderEta ELboxOptsFO
  EEtaExpand EEtaExpandSim.

Import Common.Transform.Transform.

Set Default Goal Selector "!".
#[local] Existing Instance extraction_checker_flags.

Lemma fo_unbox_ext ub ub' t :
  (forall ind c, ub ind c = ub' ind c) -> fo_blk t -> fo_unbox ub t = fo_unbox ub' t.
Proof.
  intros Hub. induction 1 using fo_blk_ind'; auto.
  cbn. rewrite Hub.
  assert (Hm : map (fo_unbox ub) args = map (fo_unbox ub') args).
  { clear H. induction H0; cbn; f_equal; auto. }
  destruct args as [|a [|b l]]; auto.
  - cbn in Hm. injection Hm as ->. reflexivity.
  - now rewrite Hm.
Qed.

Lemma fo_triple_optional' {env term : Type} {eval : program env term -> term -> Prop}
  b (o : Transform.self_transform env term eval eval)
  (P Q : program env term -> term -> Prop) :
  (b = true -> fo_triple o P Q) ->
  (b = false -> forall p v, P p v -> Q p v) ->
  fo_triple (optional_self_transform b o) P Q.
Proof.
  destruct b; intros Ht Hf; [now apply Ht|].
  intros p pr v ev HP. exists v. split; auto.
Qed.

Ltac stage :=
  apply fo_triple_obseq;
  let p := fresh "p" in let pr := fresh "pr" in
  intros p pr v v' ev HP ev' Hobs; cbn in *.

Section Prefix.
  Context {guard : PCUICWfEnvImpl.abstract_guard_impl}.
  Variable m : inductives_mapping.
  Variable Σ0 : global_declarations.
  Variable v0 : term.
  Hypothesis Hv0 : fo_app v0.

  Let Σr := EReorderCstrs.reorder_env m Σ0.

  Let npars := fo_npars Σr.
  Let shape (Σ : global_declarations) : Prop :=
    forall ind c, fo_unboxable Σ ind c = fo_unboxable Σr ind c.
  Let w1 := fo_pre m npars v0 [].
  Let w2 := fo_compile m npars v0 [].

  Lemma fo_nocofix_lambdabox_pipeline econf :
    fo_triple (nocofix_lambdabox_pipeline econf)
      (fun (p : eprogram_env) v => (p.1 : global_declarations) = Σr /\ v = EReorderCstrs.reorder m v0)
      (fun (p : eprogram) v => shape p.1 /\ v = w2).
  Proof.
    unfold nocofix_lambdabox_pipeline.
    eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w2).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => (p.1 : global_declarations) = Σr /\ v = EReorderCstrs.reorder m v0).
    - (* guarded to unguarded fixpoints *)
      stage. subst v'. exact HP.
    - (* parameter stripping *)
      stage. destruct HP as [HΣ ->]. subst v'. destruct p as [Σ t]; cbn in *. split.
      + intros ind c. unfold fo_unboxable. destruct c; auto.
        rewrite ERemoveParams.lookup_constructor_strip HΣ.
        destruct lookup_constructor as [[[? ?] ?]|]; reflexivity.
      + apply fo_strip_reorder; auto. intros ind. unfold npars. now rewrite HΣ.
    - stage. subst. exact HP.
    - (* remove match on box *)
      stage. destruct HP as [Hs ->]. subst v'. split.
      + intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
        rewrite -(EOptimizePropDiscr.lookup_constructor_remove_match_on_box
                   (efl := ERemoveParams.switch_no_params nocofix_env_flags)) //.
        apply pr.
      + apply fo_remove_match_on_box. apply fo_pre_app, Hv0.
    - stage. subst. exact HP.
    - (* projection inlining *)
      stage. destruct HP as [Hs ->]. subst v'. split.
      + intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
        rewrite -(EInlineProjections.lookup_constructor_optimize
                   (efl := ERemoveParams.switch_no_params nocofix_env_flags)) //.
        apply pr.
      + apply fo_inline_projections. apply fo_pre_app, Hv0.
    - stage. subst. exact HP.
    - (* constructors as blocks *)
      stage. destruct HP as [Hs ->]. subst v'. split.
      + intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
        rewrite EConstructorsAsBlocks.lookup_constructor_transform_blocks //.
      + unfold w2. rewrite -fo_blocks_pre //. destruct ev as [ev].
        apply eval_to_value in ev.
        refine (fo_transform_blocks
                  (efl := EInlineProjections.disable_projections_env_flag
                            (ERemoveParams.switch_no_params nocofix_env_flags))
                  _ _ _ _ _ ev);
          [reflexivity|apply pr|apply fo_pre_app, Hv0].
    - (* inlining *)
      apply fo_triple_optional; [auto|].
      unfold inlining_transformation.
      eapply fo_triple_compose with
        (Q := fun (p : inlined_program) v => shape p.1.1 /\ v = w2).
      + stage. destruct HP as [Hs ->]. subst v'. split.
        * intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
          destruct p as [Σ t]. unfold inline_program; cbn [fst snd].
          rewrite -(lookup_constr_inlining nocofix_env_flags (inlined_constants econf) Σ ind 0).
          cbn. now destruct inline_env.
        * apply fo_inline. apply fo_compile_blk, Hv0.
      + stage. subst. exact HP.
  Qed.

  Lemma fo_nocofix_lambdabox_pipeline_mapping econf :
    fo_triple (nocofix_lambdabox_pipeline_mapping econf)
      (fun (p : inductives_mapping * eprogram_env) v =>
         p.1 = m /\ (p.2.1 : global_declarations) = Σ0 /\ v = v0)
      (fun (p : eprogram) v => shape p.1 /\ v = w2).
  Proof.
    unfold nocofix_lambdabox_pipeline_mapping.
    eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v =>
              (p.1 : global_declarations) = Σr /\ v = EReorderCstrs.reorder m v0).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => p.1 = Σr /\ v = EReorderCstrs.reorder m v0).
    - stage. destruct HP as (Hm & HΣ & ->). subst v'. rewrite Hm. split; [|reflexivity].
      unfold Σr. now rewrite -HΣ.
    - stage. subst. exact HP.
    - apply fo_nocofix_lambdabox_pipeline.
  Qed.


  (** The MetaRocq pipeline on programs coming from the typed pipeline:
      as above, without the removal of matches on boxes. *)
  Lemma fo_nocofix_lambdabox_typed_pipeline econf :
    fo_triple (nocofix_lambdabox_typed_pipeline econf)
      (fun (p : inductives_mapping * eprogram_env) v =>
         p.1 = m /\ (p.2.1 : global_declarations) = Σ0 /\ v = v0)
      (fun (p : eprogram) v => shape p.1 /\ v = w2).
  Proof.
    unfold nocofix_lambdabox_typed_pipeline. cbv zeta.
    eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w2).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => shape p.1 /\ v = w1).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => (p.1 : global_declarations) = Σr /\ v = EReorderCstrs.reorder m v0).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram_env) v => (p.1 : global_declarations) = Σr /\ v = EReorderCstrs.reorder m v0).
    1: eapply fo_triple_compose with
      (Q := fun (p : eprogram) v => p.1 = Σr /\ v = EReorderCstrs.reorder m v0).
    - (* constructor reordering *)
      stage. destruct HP as (Hm & HΣ & ->). subst v'. rewrite Hm. split; [|reflexivity].
      unfold Σr. now rewrite -HΣ.
    - stage. subst. exact HP.
    - (* guarded to unguarded fixpoints *)
      stage. subst v'. exact HP.
    - (* parameter stripping *)
      stage. destruct HP as [HΣ ->]. subst v'. destruct p as [Σ t]; cbn in *. split.
      + intros ind c. unfold fo_unboxable. destruct c; auto.
        rewrite ERemoveParams.lookup_constructor_strip HΣ.
        destruct lookup_constructor as [[[? ?] ?]|]; reflexivity.
      + apply fo_strip_reorder; auto. intros ind. unfold npars. now rewrite HΣ.
    - stage. subst. exact HP.
    - (* projection inlining *)
      stage. destruct HP as [Hs ->]. subst v'. split.
      + intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
        rewrite -(EInlineProjections.lookup_constructor_optimize
                   (efl := ERemoveParams.switch_no_params nocofix_env_flags)) //.
        apply pr.
      + apply fo_inline_projections. apply fo_pre_app, Hv0.
    - stage. subst. exact HP.
    - (* constructors as blocks *)
      stage. destruct HP as [Hs ->]. subst v'. split.
      + intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
        rewrite EConstructorsAsBlocks.lookup_constructor_transform_blocks //.
      + unfold w2. rewrite -fo_blocks_pre //. destruct ev as [ev].
        apply eval_to_value in ev.
        refine (fo_transform_blocks
                  (efl := EInlineProjections.disable_projections_env_flag
                            (ERemoveParams.switch_no_params nocofix_env_flags))
                  _ _ _ _ _ ev);
          [reflexivity|apply pr|apply fo_pre_app, Hv0].
    - (* inlining *)
      apply fo_triple_optional; [auto|].
      unfold inlining_transformation.
      eapply fo_triple_compose with
        (Q := fun (p : inlined_program) v => shape p.1.1 /\ v = w2).
      + stage. destruct HP as [Hs ->]. subst v'. split.
        * intros ind c. rewrite -Hs. unfold fo_unboxable. destruct c; auto.
          destruct p as [Σ t]. unfold inline_program; cbn [fst snd].
          rewrite -(lookup_constr_inlining nocofix_env_flags (inlined_constants econf) Σ ind 0).
          cbn. now destruct inline_env.
        * apply fo_inline. apply fo_compile_blk, Hv0.
      + stage. subst. exact HP.
  Qed.

  Variable econf : erasure_configuration.

  Let w3 := if econf.(enable_unsafe).(unboxing)
            then fo_unbox (fo_unboxable Σr) w2 else w2.

  Lemma fo_nocofix_unboxing_transforms :
    fo_triple (nocofix_unboxing_transforms econf)
      (fun (p : eprogram) v => shape p.1 /\ v = w2)
      (fun _ v => v = w3).
  Proof.
    unfold nocofix_unboxing_transforms. cbv zeta.
    apply fo_triple_optional'.
    + intros Hub.
      eapply fo_triple_compose with
        (Q := fun (p : eprogram_env) v => shape p.1 /\ v = w2).
      * stage. subst. exact HP.
      * stage. destruct HP as [Hs ->]. subst v'. unfold w3. rewrite Hub.
        rewrite fo_unbox_correct; [apply fo_compile_blk, Hv0|].
        apply fo_unbox_ext; [exact Hs|apply fo_compile_blk, Hv0].
    + intros Hub p v [_ ->]. unfold w3. now rewrite Hub.
  Qed.
End Prefix.

(** Beta reduction, twice *)
Lemma fo_nocofix_betared_transforms econf w :
  fo_blk w ->
  fo_triple (nocofix_betared_transforms econf) (fun _ v => v = w) (fun _ v => v = w).
Proof.
  intros Hw. unfold nocofix_betared_transforms. cbv zeta.
  apply fo_triple_optional; [auto|].
  eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w);
    stage; subst v; (eapply fo_Gv; [exact Hw|exact Hobs]).
Qed.

(** The simplification passes after the MetaRocq pipeline *)
Lemma fo_extra_unsafe_transforms spec_inst cse lbox lift_consts impl_box impl_lazy_force w :
  fo_blk w ->
  fo_triple (extra_unsafe_transforms spec_inst cse lbox lift_consts impl_box impl_lazy_force)
    (fun _ v => v = w)
    (fun _ v => v = if impl_box then EImplementBox.implement_box w else w).
Proof.
  intros Hw. unfold extra_unsafe_transforms. cbv zeta.
  eapply fo_triple_compose with
    (Q := fun (_ : eprogram) v => v = if impl_box then EImplementBox.implement_box w else w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  1: eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
  - (* instance specialization *)
    apply fo_triple_optional; [auto|]. stage. subst v.
    eapply fo_gchain; [exact Hw|exact Hobs].
  - (* common subexpressions *)
    apply fo_triple_optional; [auto|]. stage. now subst.
  - (* iota reduction *)
    apply fo_triple_optional; [auto|]. stage. subst v.
    eapply iota_fo; [exact pr|apply (correctness iota_transformation p pr)|
                     exact Hw|exact ev|exact ev'].
  - (* identity cases *)
    apply fo_triple_optional; [auto|]. stage. subst v.
    eapply case_id_fo; [exact pr|apply (correctness case_id_transformation p pr)|
                        exact Hw|exact ev|exact ev'].
  - (* lambda-box rewritings *)
    apply fo_triple_optional; [auto|]. stage. subst v.
    eapply lbox_opts_fo; [exact pr|apply (correctness (lbox_opts_transformation lbox) p pr)|
                          exact Hw|exact ev|exact ev'].
  - (* constant lifting *)
    apply fo_triple_optional; [auto|]. stage. subst v.
    destruct ev' as [ev'].
    eapply fo_lift_rel; [exact Hw|eapply eval_to_value; exact ev'|exact Hobs].
  - (* implement box *)
    apply fo_triple_optional'.
    + intros ->. stage. now subst.
    + intros -> p v ->. reflexivity.
  - (* implement lazy/force *)
    apply fo_triple_optional; [auto|]. stage. subst.
    destruct impl_box; [apply fo_implement_lazy_force_box|apply fo_implement_lazy_force];
      exact Hw.
Qed.

(** ** The expected first-order result

    [fo_value_compile m Σ unb impl_box v] is the value the middle end computes
    from a first-order value [v] of a program with environment [Σ]:

    - constructors are renumbered by the mapping [m], their parameters are
      dropped and applications become blocks ([fo_compile]);
    - if unboxing is on, blocks of single-constructor, single-argument
      inductives are replaced by their argument ([fo_unbox]);
    - if boxes are implemented, [tBox] becomes the box constructor
      ([EImplementBox.implement_box]). *)

Definition fo_blocks_value (m : inductives_mapping) (Σ : global_declarations) (v : term) : term :=
  fo_compile m (fo_npars (EReorderCstrs.reorder_env m Σ)) v [].

Definition fo_unboxed_value (m : inductives_mapping) (Σ : global_declarations)
  (unb : bool) (v : term) : term :=
  if unb
  then fo_unbox (fo_unboxable (EReorderCstrs.reorder_env m Σ)) (fo_blocks_value m Σ v)
  else fo_blocks_value m Σ v.

Definition fo_value_compile (m : inductives_mapping) (Σ : global_declarations)
  (unb impl_box : bool) (v : term) : term :=
  if impl_box
  then EImplementBox.implement_box (fo_unboxed_value m Σ unb v)
  else fo_unboxed_value m Σ unb v.

Lemma fo_unboxed_value_blk m Σ unb v : fo_app v -> fo_blk (fo_unboxed_value m Σ unb v).
Proof.
  intros Hv. unfold fo_unboxed_value, fo_blocks_value.
  destruct unb; [apply fo_unbox_blk|]; now apply fo_compile_blk.
Qed.

(** The translation only reads the inductives of the environment, which
    eta-expansion leaves alone. *)
Lemma fo_unboxed_value_eta m Σ unb v :
  fo_app v ->
  fo_unboxed_value m (eta_expand_env Σ) unb v = fo_unboxed_value m Σ unb v.
Proof.
  intros Hv. unfold fo_unboxed_value, fo_blocks_value.
  rewrite (fo_compile_ext m _ _ (fo_npars_reorder_eta m Σ)).
  destruct unb; [|reflexivity].
  apply fo_unbox_ext; [apply fo_unboxable_reorder_eta|now apply fo_compile_blk].
Qed.

Lemma fo_value_compile_eta m Σ unb impl_box v :
  fo_app v ->
  fo_value_compile m (eta_expand_env Σ) unb impl_box v = fo_value_compile m Σ unb impl_box v.
Proof. intros Hv. unfold fo_value_compile. now rewrite fo_unboxed_value_eta. Qed.

(** The remapping of inductives is trusted: its correctness on the value at
    hand is a hypothesis.  [remap_fo econf w]: on every well-formed program
    that evaluates to [w], the remapped program evaluates to [w]. *)
Definition remap_fo (econf : erasure_configuration) (w : term) : Prop :=
  forall (p : eprogram) (wf : wf_eprogram extra_env_flags p),
    eval_eprogram final_wcbv_flags p w ->
    eval_eprogram final_wcbv_flags (remap_program econf p wf) w.

Section Main.
  Context {guard : PCUICWfEnvImpl.abstract_guard_impl}.
  Variables (econf : erasure_configuration).
  Variables (spec_inst cse : bool) (lbox : lbox_opts)
    (lift_consts impl_box impl_lazy_force : bool).

  Let unb := econf.(enable_unsafe).(unboxing).

  (** The verified prefix: up to and including unboxing *)
  Lemma fo_untyped_prefix_pipeline m Σ0 v0 :
    fo_app v0 ->
    fo_triple (untyped_prefix_pipeline econf)
      (fun (p : inductives_mapping * eprogram) v => p.1 = m /\ p.2.1 = Σ0 /\ v = v0)
      (fun _ v => v = fo_unboxed_value m Σ0 unb v0).
  Proof.
    intros Hv0. unfold untyped_prefix_pipeline.
    eapply fo_triple_compose with
      (Q := fun (p : eprogram) v =>
              (forall ind c, fo_unboxable p.1 ind c =
                             fo_unboxable (EReorderCstrs.reorder_env m Σ0) ind c) /\
              v = fo_blocks_value m Σ0 v0).
    1: eapply fo_triple_compose with
      (Q := fun (p : inductives_mapping * eprogram_env) v =>
              p.1 = m /\ (p.2.1 : global_declarations) = Σ0 /\ v = v0).
    - stage. subst. exact HP.
    - now apply fo_nocofix_lambdabox_pipeline_mapping.
    - now apply fo_nocofix_unboxing_transforms.
  Qed.

  (** The verified suffix: from beta reduction on *)
  Lemma fo_untyped_suffix_pipeline w :
    fo_blk w ->
    fo_triple (untyped_suffix_pipeline econf spec_inst cse lbox lift_consts impl_box impl_lazy_force)
      (fun _ v => v = w)
      (fun _ v => v = if impl_box then EImplementBox.implement_box w else w).
  Proof.
    intros Hw. unfold untyped_suffix_pipeline.
    eapply fo_triple_compose with (Q := fun (_ : eprogram) v => v = w).
    - now apply fo_nocofix_betared_transforms.
    - now apply fo_extra_unsafe_transforms.
  Qed.

  Let pipeline := untyped_transform_pipeline econf
    spec_inst cse lbox lift_consts impl_box impl_lazy_force.

  Lemma fo_untyped_transform_pipeline m Σ0 v0 :
    fo_app v0 ->
    fo_triple pipeline
      (fun (p : inductives_mapping * eprogram) v => p.1 = m /\ p.2.1 = Σ0 /\ v = v0)
      (fun _ v => v = fo_value_compile m Σ0 unb impl_box v0).
  Proof.
    intros Hv0. unfold pipeline, untyped_transform_pipeline.
    eapply fo_triple_compose with
      (Q := fun (_ : eprogram) v => v = fo_unboxed_value m Σ0 unb v0).
    - now apply fo_untyped_prefix_pipeline.
    - apply fo_untyped_suffix_pipeline. now apply fo_unboxed_value_blk.
  Qed.

  (** *** First-order correctness of the untyped middle end (no remapping,
      no eta-expansion) *)
  Theorem untyped_transform_pipeline_fo m (p : eprogram) (pr : pre pipeline (m, p)) v :
    fo_app v ->
    eval_eprogram default_wcbv_flags p v ->
    eval_eprogram final_wcbv_flags (transform pipeline (m, p) pr)
      (fo_value_compile m p.1 unb impl_box v).
  Proof.
    intros Hv ev.
    destruct (fo_untyped_transform_pipeline m p.1 v Hv (m, p) pr v ev)
      as (v' & ev' & ->); auto.
  Qed.

  (** Eta-expansion is the identity on saturated first-order values *)
  Lemma fo_eta_expand_transform_mapping m Σ0 v0 :
    fo_sat (fo_arity Σ0) v0 ->
    fo_triple eta_expand_transform_mapping
      (fun (p : inductives_mapping * eprogram) v => p.1 = m /\ p.2.1 = Σ0 /\ v = v0)
      (fun (p : inductives_mapping * eprogram) v =>
         p.1 = m /\ p.2.1 = eta_expand_env Σ0 /\ v = v0).
  Proof.
    intros Hv0. stage. destruct HP as (Hm & HΣ & ->).
    split; [exact Hm|]. split; [now rewrite -HΣ|].
    destruct ev' as [ev'].
    eapply fo_eta_value_rel; [|exact Hobs|eapply eval_to_value; exact ev'].
    now rewrite HΣ.
  Qed.

  Lemma fo_eta_untyped_prefix_pipeline m Σ0 v0 :
    fo_sat (fo_arity Σ0) v0 ->
    fo_triple (eta_untyped_prefix_pipeline econf)
      (fun (p : inductives_mapping * eprogram) v => p.1 = m /\ p.2.1 = Σ0 /\ v = v0)
      (fun _ v => v = fo_unboxed_value m Σ0 unb v0).
  Proof.
    intros Hv0. unfold eta_untyped_prefix_pipeline.
    eapply fo_triple_compose.
    - now apply fo_eta_expand_transform_mapping.
    - pose proof (fo_untyped_prefix_pipeline m (eta_expand_env Σ0) v0 (fo_sat_app _ _ Hv0)) as H.
      eapply fo_triple_conseq; [| |exact H].
      + intros ? ? HP; exact HP.
      + cbn. intros ? ? ->. apply fo_unboxed_value_eta. exact (fo_sat_app _ _ Hv0).
  Qed.

  Lemma fo_eta_untyped_transform_pipeline m Σ0 v0 :
    fo_sat (fo_arity Σ0) v0 ->
    fo_triple (eta_untyped_transform_pipeline econf
                 spec_inst cse lbox lift_consts impl_box impl_lazy_force)
      (fun (p : inductives_mapping * eprogram) v => p.1 = m /\ p.2.1 = Σ0 /\ v = v0)
      (fun _ v => v = fo_value_compile m Σ0 unb impl_box v0).
  Proof.
    intros Hv0. unfold eta_untyped_transform_pipeline.
    eapply fo_triple_compose.
    - now apply fo_eta_expand_transform_mapping.
    - pose proof (fo_untyped_transform_pipeline m (eta_expand_env Σ0) v0 (fo_sat_app _ _ Hv0)) as H.
      eapply fo_triple_conseq; [| |exact H].
      + intros ? ? HP; exact HP.
      + cbn. intros ? ? ->. apply fo_value_compile_eta. exact (fo_sat_app _ _ Hv0).
  Qed.
End Main.

(** ** The pipeline as run by Peregrine *)

Lemma with_check_ok {A P : Type} r (sound : Peregrine.Utils.bool_of_result r = true -> P)
  (k : P -> A) a :
  Peregrine.CheckWf.with_check r sound k = ResultMonad.Ok a -> exists pf : P, a = k pf.
Proof.
  unfold Peregrine.CheckWf.with_check. destruct r; intros H.
  - injection H as <-. eexists; reflexivity.
  - discriminate.
Qed.

Lemma join_with_check_ok {A P : Type} r (sound : Peregrine.Utils.bool_of_result r = true -> P)
  (k : P -> Peregrine.Utils.result' A) a :
  join_result (Peregrine.CheckWf.with_check r sound k) = ResultMonad.Ok a ->
  exists pf : P, k pf = ResultMonad.Ok a.
Proof.
  unfold Peregrine.CheckWf.with_check, join_result. destruct r; intros H.
  - eexists; exact H.
  - discriminate.
Qed.

(** After a prefix that produced [q] evaluating to the block value [w]: the
    trusted remapping (hypothesis [remap_fo]), the well-formedness check and
    the verified suffix. *)
Lemma remap_then_suffix_fo econf spec_inst cse lbox lift_consts impl_box impl_lazy_force
  (q : eprogram) wf p' w :
  remap_then_suffix econf spec_inst cse lbox lift_consts impl_box impl_lazy_force q wf
    = ResultMonad.Ok p' ->
  fo_blk w -> remap_fo econf w ->
  eval_eprogram final_wcbv_flags q w ->
  eval_eprogram final_wcbv_flags p'
    (if impl_box then EImplementBox.implement_box w else w).
Proof.
  unfold remap_then_suffix. cbv zeta. intros Hrun Hw Hr ev.
  apply with_check_ok in Hrun as [pf ->].
  destruct (fo_untyped_suffix_pipeline econf spec_inst cse lbox lift_consts impl_box
              impl_lazy_force w Hw _ pf w (Hr q wf ev) eq_refl) as (v' & ev' & ->).
  exact ev'.
Qed.

(** *** Main theorem (untyped pipeline, as run)

    If [run_untyped_transforms] succeeds with [p'] and the source program
    evaluates to a saturated first-order value [v], then [p'] evaluates to
    [fo_value_compile m p.1 unb impl_box v].  The correctness of the
    remapping of inductives on that value is assumed, only when a remapping
    is configured. *)
Theorem run_untyped_transforms_wf_fo {guard : PCUICWfEnvImpl.abstract_guard_impl}
  econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force (p p' : eprogram) hwf v :
  let unb := econf.(enable_unsafe).(unboxing) in
  run_untyped_transforms_wf econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force p hwf
    = ResultMonad.Ok p' ->
  fo_sat (fo_arity p.1) v ->
  (remap_on econf = true -> remap_fo econf (fo_unboxed_value m p.1 unb v)) ->
  eval_eprogram default_wcbv_flags p v ->
  eval_eprogram final_wcbv_flags p' (fo_value_compile m p.1 unb impl_box v).
Proof.
  intros unb Hrun Hv Hr ev. unfold run_untyped_transforms_wf in Hrun.
  destruct (remap_on econf).
  - apply join_with_check_ok in Hrun as [pf Hrun].
    destruct (fo_eta_untyped_prefix_pipeline econf m p.1 v Hv (m, p) pf v ev)
      as (w & evw & ->); [auto|].
    eapply remap_then_suffix_fo in Hrun; [exact Hrun| |now apply Hr|exact evw].
    apply fo_unboxed_value_blk. exact (fo_sat_app _ _ Hv).
  - apply with_check_ok in Hrun as [pf ->].
    destruct (fo_eta_untyped_transform_pipeline econf spec_inst cse lbox lift_consts impl_box
                impl_lazy_force m p.1 v Hv (m, p) pf v ev) as (w & evw & ->); [auto|].
    exact evw.
Qed.

Theorem run_untyped_transforms_fo {guard : PCUICWfEnvImpl.abstract_guard_impl}
  econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force (p p' : eprogram) v :
  let unb := econf.(enable_unsafe).(unboxing) in
  run_untyped_transforms econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force p
    = ResultMonad.Ok p' ->
  fo_sat (fo_arity p.1) v ->
  (remap_on econf = true -> remap_fo econf (fo_unboxed_value m p.1 unb v)) ->
  eval_eprogram default_wcbv_flags p v ->
  eval_eprogram final_wcbv_flags p' (fo_value_compile m p.1 unb impl_box v).
Proof.
  intros unb Hrun. unfold run_untyped_transforms in Hrun.
  apply join_with_check_ok in Hrun as [hwf Hrun].
  exact (run_untyped_transforms_wf_fo econf m spec_inst cse lbox lift_consts impl_box
           impl_lazy_force p p' hwf v Hrun).
Qed.

(** Without a configured remapping there is no hypothesis left. *)
Corollary run_untyped_transforms_fo_noremap {guard : PCUICWfEnvImpl.abstract_guard_impl}
  econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force (p p' : eprogram) v :
  let unb := econf.(enable_unsafe).(unboxing) in
  remap_on econf = false ->
  run_untyped_transforms econf m spec_inst cse lbox lift_consts impl_box impl_lazy_force p
    = ResultMonad.Ok p' ->
  fo_sat (fo_arity p.1) v ->
  eval_eprogram default_wcbv_flags p v ->
  eval_eprogram final_wcbv_flags p' (fo_value_compile m p.1 unb impl_box v).
Proof.
  intros unb Hoff Hrun Hv ev.
  eapply run_untyped_transforms_fo; eauto. rewrite Hoff. discriminate.
Qed.
