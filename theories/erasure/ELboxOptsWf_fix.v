(** * Well-formedness of the [fix_eta] lambda-box rewrite (pass 1 of [ELboxOpts])

    [wellformed_fix_eta]: [fix_eta] preserves [wellformed Σ k], assuming
    [has_tBox] (the pass substitutes boxes for the hoisted lambdas, which the
    fixpoint does not mention).  [has_tBox] holds for the pipeline flags at
    this stage. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EWellformed EInduction.
From Peregrine Require Import ELboxOpts.

Import ListNotations.
Local Open Scope bool_scope.

Section wf.
Context {efl : EEnvFlags} (Σ : global_declarations).

Lemma wf_mkApps_inv m f args :
  wellformed Σ m (mkApps f args) -> wellformed Σ m f.
Proof.
  induction args in f |- *; cbn; intros H.
  - auto.
  - specialize (IHargs _ H). cbn in IHargs.
    apply andb_true_iff in IHargs as [Hf _].
    now apply andb_true_iff in Hf as [_ Hf].
Qed.

Lemma wf_repeat_box m x : has_tBox -> forallb (wellformed Σ m) (repeat tBox x).
Proof. intros Hb. induction x; cbn; auto. Qed.

Lemma wf_strip_lambdas n b K :
  wellformed Σ K b -> wellformed Σ (Nat.min n (count_lambdas b) + K) (strip_lambdas n b).
Proof.
  induction n in b, K |- *; cbn; intros H; auto.
  destruct b; cbn; auto.
  cbn in H. apply andb_true_iff in H as [_ H].
  specialize (IHn _ _ H). now rewrite <- plus_n_Sm in IHn.
Qed.

End wf.

(** ** Main lemma *)

Lemma wellformed_fix_eta {efl : EEnvFlags} Σ k t :
  has_tBox -> wellformed Σ k t -> wellformed Σ k (fix_eta t).
Proof.
  intros Hbox H. unfold fix_eta.
  destruct (Nat.eqb (count_lambdas t) 0) eqn:Ek; [exact H|].
  pose proof (wf_strip_lambdas Σ (count_lambdas t) t k H) as H1. rewrite Nat.min_id in H1.
  destruct (decompose_app (strip_lambdas (count_lambdas t) t)) as [hd args] eqn:Ed.
  apply decompose_app_inv in Ed. rewrite Ed in H1.
  apply wf_mkApps_inv in H1.
  destruct hd; try exact H.
  destruct (_ && _) eqn:Hc; [|exact H].
  eapply wellformed_subst; [apply wf_repeat_box; exact Hbox|]. rewrite repeat_length. exact H1.
Qed.
