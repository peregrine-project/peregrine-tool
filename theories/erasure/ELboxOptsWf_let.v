(** * Well-formedness of the [let_inline] and [beta_let] rewrites of [ELboxOpts]

    Both rewrites preserve [wellformed Σ k] for every set of environment
    flags, without further hypotheses: they only permute, lift and
    substitute subterms.  [wellformed] is compositional; in particular it does
    not reject applications whose head is a constructor (also not with
    [cstr_as_blocks], which only constrains the block arguments of
    [tConstruct]), so the [mkApps hd args] built by [push_args] is harmless. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EWellformed EInduction.
From Peregrine Require Import ELboxOpts.
From Stdlib Require Import ssreflect ssrbool.

Import ListNotations.
Local Open Scope bool_scope.

(** ** [let_inline] and [beta_let] *)

Section LetFun.
  Context {efl : EEnvFlags} (Σ : global_declarations).

  Lemma wellformed_let_inline k t : wellformed Σ k t -> wellformed Σ k (let_inline t).
  Proof.
    destruct t; cbn [let_inline]; try easy.
    destruct atomic; [|easy].
    cbn [wellformed]. move/andP => [/andP [_ Hv] Hb].
    unfold subst1. apply wellformed_subst; cbn; [now rewrite Hv|exact Hb].
  Qed.

  Lemma wellformed_mkApps_head j f args : wellformed Σ j (mkApps f args) -> wellformed Σ j f.
  Proof.
    induction args in f |- *; cbn; [easy|].
    intros H. apply IHargs in H. cbn in H. by move/andP: H => [/andP [_ ?] _].
  Qed.

  Lemma wellformed_mkApps_has_tApp j f a args :
    wellformed Σ j (mkApps f (a :: args)) -> has_tApp.
  Proof.
    cbn. intros H. apply wellformed_mkApps_head in H. cbn in H.
    now apply andb_and in H as [H _]; apply andb_and in H as [? _].
  Qed.

  (** [push_args] only builds lets, substitutions and applications. *)
  Lemma wellformed_push_args fuel j hd args :
    has_tApp -> wellformed Σ j hd -> forallb (wellformed Σ j) args ->
    wellformed Σ j (push_args fuel hd args).
  Proof.
    intros hasapp.
    induction fuel in j, hd, args |- *; intros Hhd Hargs; cbn [push_args].
    - rewrite wellformed_mkApps //. now rewrite Hhd Hargs.
    - destruct args as [|a rest]; [assumption|].
      destruct hd; try (rewrite wellformed_mkApps //; now rewrite Hhd Hargs).
      + (* tLambda: beta reduction *)
        cbn in Hhd, Hargs. apply andb_and in Hhd as [_ Hb].
        apply andb_and in Hargs as [Ha Hrest].
        apply IHfuel; [|assumption].
        unfold subst1. apply wellformed_subst; cbn; [now rewrite Ha|exact Hb].
      + (* tLetIn: push the lifted arguments under the let *)
        cbn [wellformed] in Hhd |- *. apply andb_and in Hhd as [Hhd Hb].
        apply andb_and in Hhd as [hlet Hv]. rewrite hlet Hv; cbn [andb].
        apply IHfuel; [assumption|].
        rewrite forallb_map. eapply forallb_impl; [|exact Hargs].
        intros x _ Hx. rewrite -(Nat.add_1_r j). now apply wellformed_lift.
  Qed.

  Lemma wellformed_beta_let k t : wellformed Σ k t -> wellformed Σ k (beta_let t).
  Proof.
    unfold beta_let. destruct (decompose_app t) as [hd args] eqn:da.
    apply decompose_app_inv in da. subst t. intros H.
    destruct args as [|a rest]; [destruct hd; exact H|].
    pose proof (wellformed_mkApps_has_tApp _ _ _ _ H) as hasapp.
    pose proof H as H'.
    rewrite wellformed_mkApps // in H. apply andb_and in H as [Hhd Hargs].
    destruct hd; try exact H'.
    - (* tLambda *)
      destruct (forallb atomic _); [|exact H'].
      now apply wellformed_push_args.
    - (* tLetIn *)
      destruct (forallb atomic _); [|exact H'].
      now apply wellformed_push_args.
    - (* tCase: push the lifted arguments into every branch *)
      destruct (forallb atomic _ && _); [|exact H'].
      cbn [wellformed] in Hhd |- *. move: Hhd => /andP [hcase /andP [/andP [hbrs hc] hbr]].
      rewrite hcase length_map hbrs hc; cbn [andb].
      rewrite forallb_map. eapply forallb_impl; [|exact hbr].
      intros br _ Hbr. apply wellformed_push_args; [assumption|assumption|].
      rewrite forallb_map. eapply forallb_impl; [|exact Hargs].
      intros x _ Hx. rewrite Nat.add_comm. now apply wellformed_lift.
  Qed.

End LetFun.
