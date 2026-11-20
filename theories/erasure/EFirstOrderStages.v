(** * The MetaRocq term transformations on first-order values

    Closed forms of the term transformations of the verified λ□ stages
    (constructor reordering, parameter stripping, removal of matches on [□],
    projection inlining, constructors as blocks, inlining, unboxing,
    [□]-implementation, lazy/force) on first-order values. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed EEnvMap EEtaExpanded EInlining.
From MetaRocq.Erasure Require EReorderCstrs ERemoveParams EOptimizePropDiscr
  EInlineProjections EConstructorsAsBlocks EUnboxing EImplementBox EImplementLazyForce.
From Peregrine Require Import EFirstOrder.

Set Default Goal Selector "!".

(** Number of parameters to drop, read off an environment. *)
Definition fo_npars (Σ : global_declarations) (ind : inductive) : nat :=
  match lookup_inductive_pars Σ (inductive_mind ind) with
  | Some n => n
  | None => 0
  end.

(** Which constructors unboxing removes, read off an environment. *)
Definition fo_unboxable (Σ : global_declarations) (ind : inductive) (c : nat) : bool :=
  match c with
  | 0 => match lookup_constructor Σ ind 0 with
         | Some (_, idecl, cdecl) => EUnboxing.unboxable idecl cdecl
         | None => false
         end
  | S _ => false
  end.

(** Intermediate closed forms: reordering and parameter stripping, then
    blocks. *)
Fixpoint fo_pre (m : inductives_mapping) (npars : inductive -> nat)
  (t : term) (acc : list term) : term :=
  match t with
  | tApp f a => fo_pre m npars f (fo_pre m npars a [] :: acc)
  | tConstruct ind c _ =>
      mkApps (tConstruct ind (EReorderCstrs.lookup_constructor_ordinal m ind c) [])
        (skipn (npars ind) acc)
  | _ => t
  end.

Fixpoint fo_blocks (t : term) (acc : list term) : term :=
  match t with
  | tApp f a => fo_blocks f (fo_blocks a [] :: acc)
  | tConstruct ind c _ => tConstruct ind c acc
  | _ => t
  end.

Lemma fo_pre_mkApps m npars f l acc :
  fo_pre m npars (mkApps f l) acc =
  fo_pre m npars f (map (fun a => fo_pre m npars a []) l ++ acc).
Proof.
  revert f acc. induction l using rev_ind; intros f acc; cbn; auto.
  rewrite mkApps_app /= IHl map_app /= -app_assoc //.
Qed.

Lemma fo_blocks_mkApps f l acc :
  fo_blocks (mkApps f l) acc = fo_blocks f (map (fun a => fo_blocks a []) l ++ acc).
Proof.
  revert f acc. induction l using rev_ind; intros f acc; cbn; auto.
  rewrite mkApps_app /= IHl map_app /= -app_assoc //.
Qed.

Lemma map_skipn' {A B} (f : A -> B) n l : map f (skipn n l) = skipn n (map f l).
Proof. revert l; induction n; intros [|x l]; cbn; auto; apply IHn. Qed.

Lemma fo_pre_app m npars t : fo_app t -> fo_app (fo_pre m npars t []).
Proof.
  induction 1 using fo_app_ind'; try solve [constructor; auto].
  rewrite fo_pre_mkApps /= app_nil_r. constructor.
  apply Forall_skipn'. now apply Forall_map.
Qed.

Lemma fo_blocks_pre m npars t :
  fo_app t -> fo_blocks (fo_pre m npars t []) [] = fo_compile m npars t [].
Proof.
  induction 1 using fo_app_ind'; auto.
  rewrite fo_pre_mkApps fo_compile_construct /= app_nil_r fo_blocks_mkApps /= app_nil_r.
  f_equal. rewrite -(Forall_map_eq _ _ _ H0) map_skipn' map_map //.
Qed.

(** Reordering then parameter stripping *)
Lemma fo_reorder m t : fo_app t -> fo_app (EReorderCstrs.reorder m t).
Proof.
  induction 1 using fo_app_ind'.
  - constructor.
  - cbn. rewrite fo_prim_map //. now constructor.
  - rewrite EReorderCstrs.optimize_mkApps /=. constructor. now apply Forall_map.
Qed.

Lemma fo_strip_reorder m (Σ : GlobalContextMap.t) npars t :
  (forall ind, npars ind = fo_npars Σ ind) ->
  fo_app t ->
  ERemoveParams.strip Σ (EReorderCstrs.reorder m t) = fo_pre m npars t [].
Proof.
  intros Hn.
  induction 1 using fo_app_ind'.
  - reflexivity.
  - cbn. rewrite fo_prim_map //. destruct p as [? []]; cbn in *; try reflexivity. destruct H.
  - rewrite EReorderCstrs.optimize_mkApps /= ERemoveParams.strip_mkApps //=.
    rewrite fo_pre_mkApps /= app_nil_r Hn /fo_npars.
    rewrite map_map.
    rewrite (Forall_map_eq _ (fun a => fo_pre m npars a []) args) //.
    destruct lookup_inductive_pars; reflexivity.
Qed.

Ltac fo_prim_tac :=
  match goal with
  | [ H : fo_prim ?p |- _ ] =>
      destruct p as [? []]; cbn in *; try reflexivity; try (now exfalso)
  end.

(** Removal of matches on [□] and projection inlining are the identity *)
Lemma fo_remove_match_on_box Σ t :
  fo_app t -> EOptimizePropDiscr.remove_match_on_box Σ t = t.
Proof.
  induction 1 using fo_app_ind'.
  - reflexivity.
  - fo_prim_tac.
  - rewrite EOptimizePropDiscr.remove_match_on_box_mkApps /=. f_equal.
    now apply Forall_map_id.
Qed.

Lemma fo_inline_projections Σ t :
  fo_app t -> EInlineProjections.optimize Σ t = t.
Proof.
  induction 1 using fo_app_ind'.
  - reflexivity.
  - fo_prim_tac.
  - rewrite EInlineProjections.optimize_mkApps /=. f_equal.
    now apply Forall_map_id.
Qed.

(** Constructors as blocks *)
Lemma chop_all {A} n (l : list A) : #|l| <= n -> chop n l = (l, []).
Proof.
  revert l; induction n; intros [|x l] Hl; cbn in *; auto; try lia.
  rewrite IHn //. lia.
Qed.

Section Blocks.
  Context {wfl : WcbvFlags} {efl : EEnvFlags}.
  Hypothesis Hblock : with_constructor_as_block = false.
  Hypothesis Hpars : has_cstr_params = false.

  Lemma fo_transform_blocks (Σ : GlobalContextMap.t) t :
    wf_glob Σ ->
    fo_app t -> value Σ t ->
    EConstructorsAsBlocks.transform_blocks Σ t = fo_blocks t [].
  Proof.
    intros wfΣ.
    induction 1 using fo_app_ind'; intros Hv.
    - reflexivity.
    - fo_prim_tac.
    - rewrite EConstructorsAsBlocks.transform_blocks_mkApps //=.
      rewrite fo_blocks_mkApps /= app_nil_r.
      apply value_mkApps_inv in Hv as [[[-> Hat]|[-> _]]|[Hne Hhd Hall]] => //.
      + cbn. destruct lookup_constructor_pars_args as [[? []]|]; reflexivity.
      + cbn. destruct lookup_constructor_pars_args as [[? []]|]; reflexivity.
      + assert (Hmap : map (EConstructorsAsBlocks.transform_blocks Σ) args =
                       map (fun a => fo_blocks a []) args).
        { apply Forall_map_eq. clear -H0 Hall.
          induction Hall; inversion H0; subst; constructor; auto. }
        rewrite Hmap.
        depelim Hhd.
        rewrite /lookup_constructor_pars_args e0 /=.
        assert (Hp : ind_npars mdecl = 0).
        { move: e0. rewrite /lookup_constructor /lookup_inductive.
          destruct lookup_minductive as [m'|] eqn:Hm => //=.
          destruct (nth_error (ind_bodies m') _) => //=.
          destruct (nth_error (ind_ctors _) _) => //=. intros [= <- _ _].
          eapply EImplementBox.wellformed_lookup_inductive_pars; tea. }
        rewrite chop_all //.
        rewrite length_map. move: l. rewrite /cstr_arity. lia.
  Qed.
End Blocks.

(** Inlining is the identity on blocks *)
Lemma fo_inline Σ t : fo_blk t -> inline Σ t = t.
Proof.
  induction 1 using fo_blk_ind'.
  - reflexivity.
  - fo_prim_tac.
  - cbn. f_equal. now apply Forall_map_id.
Qed.

(** Unboxing *)
Lemma is_unboxable_fo (Σ : GlobalContextMap.t) ind c :
  EUnboxing.is_unboxable Σ ind c = fo_unboxable Σ ind c.
Proof.
  destruct c; simp is_unboxable; cbn; auto.
  rewrite GlobalContextMap.lookup_constructor_spec.
  destruct lookup_constructor as [[[]]|]; reflexivity.
Qed.

Lemma fo_unbox_correct (Σ : GlobalContextMap.t) t :
  fo_blk t -> EUnboxing.unbox Σ t = fo_unbox (fo_unboxable Σ) t.
Proof.
  induction 1 using fo_blk_ind'.
  - reflexivity.
  - fo_prim_tac.
  - assert (Hmap : map (EUnboxing.unbox Σ) args = map (fo_unbox (fo_unboxable Σ)) args)
      by now apply Forall_map_eq.
    rewrite -/(fo_unbox (fo_unboxable Σ)) in Hmap.
    destruct args as [|a [|b l]]; simp unbox; cbn.
    + destruct (EUnboxing.is_unboxable Σ ind c); reflexivity.
    + rewrite -is_unboxable_fo. inversion H0; subst.
      destruct (EUnboxing.is_unboxable Σ ind c); cbn; congruence.
    + cbn in Hmap. destruct (EUnboxing.is_unboxable Σ ind c); cbn; congruence.
Qed.

(** Implementation of [□] and of lazy/force *)
Lemma fo_implement_lazy_force t :
  fo_blk t -> EImplementLazyForce.implement_lazy_force t = t.
Proof.
  induction 1 using fo_blk_ind'.
  - reflexivity.
  - fo_prim_tac.
  - simp implement_lazy_force. f_equal. 
    now apply Forall_map_id.
Qed.

Lemma fo_implement_lazy_force_box t :
  fo_blk t ->
  EImplementLazyForce.implement_lazy_force (EImplementBox.implement_box t) =
  EImplementBox.implement_box t.
Proof.
  induction 1 using fo_blk_ind'.
  - reflexivity.
  - fo_prim_tac.
  - simp implement_box. simp implement_lazy_force. f_equal.
    rewrite ?map_InP_spec ?map_map.
    now apply Forall_map_eq.
Qed.
