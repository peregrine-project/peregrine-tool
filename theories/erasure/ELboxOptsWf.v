(** * Well-formedness of the lambda-box simplifications ([ELboxOpts])

    [optimize o] preserves [wellformed], [optimize_env o] preserves [wf_glob],
    and [lbox_opts_program o] preserves [wf_eprogram], given that each local
    rewrite of [rewrite_node] preserves [wellformed].  The latter are the five
    per-rewrite lemmas [wellformed_fix_eta] ([ELboxOptsWf_fix]),
    [wellformed_case_fun] and [wellformed_case_id] ([ELboxOptsWf_case]), and
    [wellformed_let_inline] and [wellformed_beta_let] ([ELboxOptsWf_let]).

    Threading extra hypotheses of the per-rewrite lemmas: the composition is
    generic over [rewrite_node_wf efl o], which may assume [wf_glob Σ].  Only
    [wellformed_rewrite_node] combines the five lemmas; a flag hypothesis on
    [efl] (such as [has_tBox] for [fix_eta]) is a premise there and is
    discharged at [extra_env_flags] by computation in [rewrite_node_wf_extra].

    The pipeline transformations [case_id_transformation] and
    [lbox_opts_transformation] are at the end of this file. *)

From Stdlib Require Import List Bool Arith ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EProgram EWellformed EWcbvEval EGlobalEnv EBeta EInduction.
From Peregrine Require Import ELboxOpts ELboxOptsSim ELboxOptsSimStatic ELboxOptsWf_case ELboxOptsWf_fix ELboxOptsWf_let EExtraFlags.

Import ListNotations.
Local Open Scope bool_scope.
Set Default Goal Selector "!".

(** ** One node *)

Definition rewrite_node_wf (efl : EEnvFlags) (o : lbox_opts) : Prop :=
  forall Σ, wf_glob Σ -> forall k t, wellformed Σ k t -> wellformed Σ k (rewrite_node o t).

Lemma wellformed_rewrite_node {efl : EEnvFlags} o :
  has_tBox -> has_tLetIn -> rewrite_node_wf efl o.
Proof.
  intros hbox hlet Σ wfΣ k t wft.
  destruct t; cbn [rewrite_node]; auto.
  - destruct lbox_fix_eta; auto using wellformed_fix_eta.
  - destruct lbox_let_fun; auto using wellformed_let_inline.
  - destruct lbox_let_fun; auto using wellformed_beta_let.
  - destruct lbox_iota; [now apply wellformed_iota_case|].
    destruct lbox_case_fun, lbox_case_id; auto using wellformed_case_fun, wellformed_case_id.
Qed.

(** At the flags of the pipeline (flag hypotheses are discharged here). *)
Lemma rewrite_node_wf_extra o : rewrite_node_wf extra_env_flags o.
Proof. apply wellformed_rewrite_node; reflexivity. Qed.

(** ** Terms *)

Lemma optimize_unfold o t : optimize o t = rewrite_node o (map_subterms_fix (optimize o) t).
Proof. destruct t; reflexivity. Qed.

Lemma optimize_fix_body_lambda f b :
  isLambda b -> optimize_fix_body f b = map_subterms_fix f b.
Proof. destruct b => //. Qed.

Section optimize.
  Context {efl : EEnvFlags} (o : lbox_opts) (Σ : global_context).
  Hypothesis wf_node : forall k t, wellformed Σ k t -> wellformed Σ k (rewrite_node o t).

  (* Both the optimized term and its optimized immediate subterms (the latter
     is what a fixpoint body gets, see [optimize_fix_body]). *)
  Definition wf_opt t := forall k, wellformed Σ k t ->
    wellformed Σ k (optimize o t) /\ wellformed Σ k (map_subterms_fix (optimize o) t).

  Lemma wf_opt_optimize t k : wf_opt t -> wellformed Σ k t -> wellformed Σ k (optimize o t).
  Proof. intros h wft. now apply h. Qed.

  Lemma wf_opt_fix_body t k : wf_opt t -> isLambda t -> wellformed Σ k t ->
    wellformed Σ k (optimize_fix_body (optimize o) t).
  Proof. intros h hl wft. rewrite optimize_fix_body_lambda //. now apply h. Qed.

  Lemma isLambda_optimize_fix_body f t : isLambda t -> isLambda (optimize_fix_body f t).
  Proof. destruct t => //. Qed.

  Lemma wf_opt_intro t :
    (forall k, wellformed Σ k t -> wellformed Σ k (map_subterms_fix (optimize o) t)) -> wf_opt t.
  Proof.
    intros h k wft. split; [rewrite optimize_unfold; apply wf_node|]; now apply h.
  Qed.

  #[local] Hint Resolve wf_opt_optimize wf_opt_fix_body isLambda_optimize_fix_body : core.

  Lemma wellformed_optimize_gen t : wf_opt t.
  Proof.
    induction t using term_forall_list_ind; apply wf_opt_intro; intros k wft;
      cbn [map_subterms_fix map_subterms wellformed] in *; rtoProp; intuition eauto.
    all: try solve [solve_all].
    - (* tConstruct *)
      destruct cstr_as_blocks.
      + rewrite length_map. rtoProp; split.
        * destruct lookup_constructor_pars_args as [[]|] => //.
        * solve_all.
      + now destruct args.
    - (* tFix *)
      unfold wf_fix_gen in *. rtoProp. rewrite length_map. split => //.
      solve_all. unfold test_def, map_def in *; cbn in *. now apply wf_opt_fix_body.
    - (* tCoFix *)
      unfold wf_fix_gen in *. rtoProp. rewrite length_map. split => //.
      solve_all. unfold test_def, map_def in *; cbn in *. now apply wf_opt_optimize.
    - (* tPrim *)
      rewrite test_prim_map. eapply primProp_impl_test_prim.
      match goal with h : is_true (test_prim _ _) |- _ => eapply test_prim_impl_primProp in h;
        eapply primProp_impl; [exact (primProp_conj X h)|] end.
      cbn. intros x [h1 h2]. now apply h1.
  Qed.

  Lemma wellformed_optimize k t : wellformed Σ k t -> wellformed Σ k (optimize o t).
  Proof. now apply wellformed_optimize_gen. Qed.
End optimize.

(** ** Environments *)

Section env.
  Context (o : lbox_opts).

  Lemma lookup_env_optimize_env Σ kn :
    lookup_env (optimize_env o Σ) kn = option_map (optimize_decl o) (lookup_env Σ kn).
  Proof.
    induction Σ as [|[kn' d] Σ IH]; cbn => //.
    now destruct eq_kername.
  Qed.

  Lemma lookup_minductive_optimize_env Σ kn :
    lookup_minductive (optimize_env o Σ) kn = lookup_minductive Σ kn.
  Proof.
    unfold lookup_minductive. rewrite lookup_env_optimize_env.
    now destruct lookup_env as [[]|].
  Qed.

  Lemma lookup_inductive_optimize_env Σ ind :
    lookup_inductive (optimize_env o Σ) ind = lookup_inductive Σ ind.
  Proof. unfold lookup_inductive. now rewrite lookup_minductive_optimize_env. Qed.

  Lemma lookup_constructor_optimize_env Σ ind c :
    lookup_constructor (optimize_env o Σ) ind c = lookup_constructor Σ ind c.
  Proof. unfold lookup_constructor. now rewrite lookup_inductive_optimize_env. Qed.

  Lemma lookup_constructor_pars_args_optimize_env Σ ind c :
    lookup_constructor_pars_args (optimize_env o Σ) ind c = lookup_constructor_pars_args Σ ind c.
  Proof. unfold lookup_constructor_pars_args. now rewrite lookup_constructor_optimize_env. Qed.

  Lemma lookup_projection_optimize_env Σ p :
    lookup_projection (optimize_env o Σ) p = lookup_projection Σ p.
  Proof. unfold lookup_projection. now rewrite lookup_constructor_optimize_env. Qed.

  Lemma lookup_constant_optimize_env Σ kn :
    lookup_constant (optimize_env o Σ) kn =
    option_map (fun cb => {| cst_body := option_map (optimize o) cb.(cst_body) |}) (lookup_constant Σ kn).
  Proof.
    unfold lookup_constant. rewrite lookup_env_optimize_env.
    now destruct lookup_env as [[]|].
  Qed.

  Lemma wellformed_optimize_env {efl : EEnvFlags} Σ k t :
    wellformed Σ k t -> wellformed (optimize_env o Σ) k t.
  Proof.
    induction t in k |- * using term_forall_list_ind; intros wft;
      cbn -[lookup_constant lookup_constructor lookup_constructor_pars_args lookup_projection lookup_inductive] in *;
      unfold wf_brs in *;
      rewrite ?lookup_constant_optimize_env ?lookup_constructor_optimize_env
        ?lookup_constructor_pars_args_optimize_env ?lookup_projection_optimize_env
        ?lookup_inductive_optimize_env;
      rtoProp; intuition eauto.
    all: try solve [unfold wf_fix_gen in *; rtoProp; intuition eauto; solve_all].
    - destruct lookup_constant as [[[]]|] => //.
    - destruct cstr_as_blocks => //. rtoProp; intuition eauto. solve_all.
  Qed.

  Lemma fresh_global_optimize_env kn Σ :
    fresh_global kn Σ -> fresh_global kn (optimize_env o Σ).
  Proof.
    unfold fresh_global, optimize_env. intros h.
    eapply Forall_map, Forall_impl; [exact h|]. now intros [].
  Qed.

  Lemma wf_glob_optimize_env {efl : EEnvFlags} :
    rewrite_node_wf efl o -> forall Σ, wf_glob Σ -> wf_glob (optimize_env o Σ).
  Proof.
    intros hnode Σ wfΣ. induction wfΣ as [|kn d Σ wfΣ IH hd hfresh]; cbn; constructor; auto.
    - destruct d as [[[b|]]|] => //; cbn in *.
      apply wellformed_optimize_env, wellformed_optimize => //. now apply hnode.
    - now apply fresh_global_optimize_env.
  Qed.

  Lemma wf_eprogram_lbox_opts_program {efl : EEnvFlags} :
    rewrite_node_wf efl o -> forall p, wf_eprogram efl p -> wf_eprogram efl (lbox_opts_program o p).
  Proof.
    intros hnode [Σ t] [wfΣ wft]; cbn in *. split.
    - now apply wf_glob_optimize_env.
    - apply wellformed_optimize_env, wellformed_optimize => //. now apply hnode.
  Qed.
End env.

(** ** Pipeline transformations

    Stated at the flags of the pipeline stage ([EExtraFlags]).

    Evaluation is preserved by all four rewrites (fixpoint eta-hoisting,
    identity-case, case/function, atomic-let inlining with beta/let): if the
    source program evaluates to [v], the target program evaluates to some
    [v'] with [lbox_obs v v'], where [lbox_obs] is a chain of steps of the
    rewrite relation [R] of [ELboxOptsSim] ("[v'] is [v] with some subterms
    rewritten").  A stronger relation such as [v' = optimize o v] is false
    once the value is a closure, since substitution creates and destroys
    redexes of the pass.

    This is proved in [ELboxOptsSim] (the relation), [ELboxOptsSimEval] (the
    simulation) and [ELboxOptsSimStatic] (the passes are chains of steps). *)

(** Evaluation preservation at the pipeline flags, for any set of rewrites
    whose node rewrite is a step of the rewrite relation [R] of [ELboxOptsSim]:
    the values are related by [lbox_obs], a chain of such steps. *)
Definition lbox_obs : term -> term -> Prop := obs (wfl := extra_wcbv_flags).

Lemma lbox_opts_program_eval (o : lbox_opts) :
  (forall t, chain (wfl := extra_wcbv_flags) t (rewrite_node o t)) ->
  forall (p : program) (v : term),
  wf_eprogram extra_env_flags p ->
  eval_eprogram extra_wcbv_flags p v ->
  exists v', eval_eprogram extra_wcbv_flags (lbox_opts_program o p) v' /\ lbox_obs v v'.
Proof.
  intros Hnode p v [wfΣ wft] [ev].
  unfold eval_eprogram, lbox_obs.
  refine (lbox_opts_program_pres (wfl := extra_wcbv_flags) eq_refl eq_refl eq_refl o Hnode p v _ _ _ ev).
  - now eapply wellformed_closed_env.
  - intros kn mdecl. now eapply (EImplementBox.wellformed_lookup_inductive_pars (efl := extra_env_flags)).
  - now eapply wellformed_closed.
Qed.

Lemma case_id_terminates :
  forall (p : program) (v : term),
  wf_eprogram extra_env_flags p ->
  eval_eprogram extra_wcbv_flags p v ->
  exists v', eval_eprogram extra_wcbv_flags (lbox_opts_program case_id_opts p) v' /\ lbox_obs v v'.
Proof. apply lbox_opts_program_eval, case_id_node. Qed.

Lemma lbox_opts_eval (o : lbox_opts) :
  forall (p : program) (v : term),
  wf_eprogram extra_env_flags p ->
  eval_eprogram extra_wcbv_flags p v ->
  exists v', eval_eprogram extra_wcbv_flags (lbox_opts_program (without_case_id o) p) v' /\
    lbox_obs v v'.
Proof. apply lbox_opts_program_eval, lbox_node. Qed.

Import MetaRocq.Common.Transform.Transform.

(** Fixpoint eta-hoisting, case/function permutation and atomic/applied lets (the
    identity-case component of [o] is ignored, see [case_id_transformation]). *)
Program Definition lbox_opts_transformation (o : lbox_opts) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram extra_wcbv_flags) (eval_eprogram extra_wcbv_flags) :=
  {| name := "lambda-box simplifications (fix eta, case/fun, let/fun)";
     transform p _ := lbox_opts_program (without_case_id o) p;
     pre p := wf_eprogram extra_env_flags p;
     post p := wf_eprogram extra_env_flags p;
     obseq _ _ _ v v' := lbox_obs v v' |}.
Next Obligation.
  intros. apply wf_eprogram_lbox_opts_program => //. apply rewrite_node_wf_extra.
Qed.
Next Obligation.
  intros. cbn. now apply lbox_opts_eval.
Qed.

Program Definition case_id_transformation :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram extra_wcbv_flags) (eval_eprogram extra_wcbv_flags) :=
  {| name := "lambda-box identity cases";
     transform p _ := lbox_opts_program case_id_opts p;
     pre p := wf_eprogram extra_env_flags p;
     post p := wf_eprogram extra_env_flags p;
     obseq _ _ _ v v' := lbox_obs v v' |}.
Next Obligation.
  intros. apply wf_eprogram_lbox_opts_program => //. apply rewrite_node_wf_extra.
Qed.
Next Obligation.
  intros. cbn. now apply case_id_terminates.
Qed.

(** Generalised iota (constructor scrutinees, case-of-let, case-of-case). *)
Program Definition iota_transformation :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram extra_wcbv_flags) (eval_eprogram extra_wcbv_flags) :=
  {| name := "lambda-box generalised iota";
     transform p _ := lbox_opts_program iota_opts p;
     pre p := wf_eprogram extra_env_flags p;
     post p := wf_eprogram extra_env_flags p;
     obseq _ _ _ v v' := lbox_obs v v' |}.
Next Obligation.
  intros. apply wf_eprogram_lbox_opts_program => //. apply rewrite_node_wf_extra.
Qed.
Next Obligation.
  intros. cbn. subst p'. apply lbox_opts_program_eval; [intros; apply lbox_node|assumption..].
Qed.
