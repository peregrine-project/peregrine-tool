From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonComplete.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import SerializePrimitivesComplete.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From Ceres Require Import CeresUtils.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure Require EInduction.
From Stdlib Require Import List.



Instance Complete_def {T : Set} `{CompleteClass T} : CompleteClass (def T).
Proof.
  unfold CompleteClass, Complete.
  intros l d.
  cbn -[Deserialize_name Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  destruct d; cbn.
  reflexivity.
Qed.

Instance Complete_mfixpoint {T : Set} `{CompleteClass T} : CompleteClass (mfixpoint T).
Proof.
  unfold CompleteClass, Complete.
  intros l d.
  cbn.
  apply complete_class_list.
Qed.


Lemma complete_class_def_all : forall m,
  All_Forall.All
    (fun x : def term =>
      forall l : loc, _from_sexp l (to_sexp (dbody x)) = inr (dbody x)) m ->
  All_Forall.All
    (fun t : def term =>
    forall l : loc, _from_sexp l (to_sexp t) = inr t) m.
Proof.
  intros.
  eapply All_Forall.All_impl.
  apply X.
  intros.
  cbn in H.
  cbn -[Deserialize_name Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite H.
  rewrite 2!complete_class.
  destruct x; cbn.
  reflexivity.
Qed.

Lemma complete_class_prim_val_all {T : Set} {H : Serialize T} {H0 : Deserialize T}
: forall (p : EPrimitive.prim_val T) l (f : EPrimitive.prim_val T -> T),
  EPrimitive.primProp (fun t : T => forall l : loc, _from_sexp l (to_sexp t) = inr t) p ->
  _bind_sum (_from_sexp (0 :: l) (to_sexp p))
    (fun a : EPrimitive.prim_val T => inr (f a)) = inr (f p).
Proof.
  intros.
  destruct p.
  destruct p.
  - cbn -[Deserialize_prim_int].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_prim_float].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_prim_string].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - inversion_clear X; subst.
    destruct X0 as [H1 H2].
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite H1.
    rewrite complete_class_list_all by assumption.
    destruct a; cbn.
    reflexivity.
Qed.

Instance Complete_term : CompleteClass term.
Proof.
  unfold CompleteClass, Complete.
  intros l t.
  revert l.
  induction t using EInduction.term_forall_list_ind; intros loc.
  - (* tBox *)
    reflexivity.
  - (* tRel *)
    cbn -[Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
  - (* tVar *)
    cbn -[Deserialize_ident].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - (* tEvar *)
    cbn -[Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    rewrite complete_class_list_all by assumption.
    reflexivity.
  - (* tLambda *)
    cbn -[Deserialize_name].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    rewrite IHt.
    reflexivity.
  - (* tLetIn *)
    cbn -[Deserialize_name].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* tApp *)
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite IHt1, IHt2.
    reflexivity.
  - (* tConst *)
    cbn -[Deserialize_kername].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - (* tConstruct *)
    cbn -[Deserialize_inductive Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite 2!complete_class.
    rewrite complete_class_list_all by assumption.
    reflexivity.
  - (* tCase *)
    cbn -[Deserialize_inductive Deserialize_SemiIntegral Deserialize_name Deserialize_prod].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    rewrite IHt.
    cbn.
    rewrite complete_class_list_all.
    reflexivity.
    apply complete_class_all_prod; try assumption.
    typeclasses eauto.
  - (* tProj *)
    cbn -[Deserialize_projection].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    rewrite IHt.
    reflexivity.
  - (* tFix *)
    cbn -[Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class_list_all.
    + rewrite complete_class.
      reflexivity.
    + apply complete_class_def_all.
      assumption.
  - (* tCoFix *)
    cbn -[Deserialize_SemiIntegral].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class_list_all.
    + rewrite complete_class.
      reflexivity.
    + apply complete_class_def_all.
      assumption.
  - (* tPrim *)
    cbn -[Deserialize_prim_val].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.

    destruct p.
    destruct p.
    + cbn -[Deserialize_prim_int].
      rewrite !eqb_ascii_refl.
      rewrite complete_class.
      reflexivity.
    + cbn -[Deserialize_prim_float].
      rewrite !eqb_ascii_refl.
      rewrite !neqb_ascii_neq by congruence.
      rewrite complete_class.
      reflexivity.
    + cbn -[Deserialize_prim_string].
      rewrite !eqb_ascii_refl.
      rewrite !neqb_ascii_neq by congruence.
      rewrite complete_class.
      reflexivity.
    + inversion_clear X; subst.
      destruct X0 as [H1 H2].
      cbn.
      rewrite !eqb_ascii_refl.
      rewrite !neqb_ascii_neq by congruence.
      rewrite H1.
      rewrite complete_class_list_all by assumption.
      destruct a; cbn.
      reflexivity.
  - (* tLazy *)
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite IHt.
    reflexivity.
  - (* tForce *)
    cbn.
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite IHt.
    reflexivity.
Qed.



Instance Complete_constructor_body : CompleteClass constructor_body.
Proof.
  unfold CompleteClass, Complete.
  intros l cb.
  cbn -[Deserialize_ident Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 2!complete_class.
  destruct cb; cbn.
  reflexivity.
Qed.

Instance Complete_projection_body : CompleteClass projection_body.
Proof.
  unfold CompleteClass, Complete.
  intros l pb.
  cbn -[Deserialize_ident].
  rewrite !eqb_ascii_refl.
  rewrite 1!complete_class.
  destruct pb; cbn.
  reflexivity.
Qed.

Instance Complete_one_inductive_body : CompleteClass one_inductive_body.
Proof.
  unfold CompleteClass, Complete.
  intros l oib.
  cbn -[Deserialize_ident Deserialize_bool Deserialize_allowed_eliminations].
  rewrite !eqb_ascii_refl.
  rewrite 3!complete_class.
  rewrite 2!complete_class_list.
  destruct oib; cbn.
  reflexivity.
Qed.

Instance Complete_mutual_inductive_body : CompleteClass mutual_inductive_body.
Proof.
  unfold CompleteClass, Complete.
  intros l mib.
  cbn -[Deserialize_recursivity_kind Deserialize_SemiIntegral].
  rewrite !eqb_ascii_refl.
  rewrite 2!complete_class.
  rewrite 1!complete_class_list.
  destruct mib; cbn.
  reflexivity.
Qed.

Instance Complete_constant_body : CompleteClass constant_body.
Proof.
  unfold CompleteClass, Complete.
  intros l cb.
  cbn -[Deserialize_option].
  rewrite !eqb_ascii_refl.
  rewrite 1!complete_class.
  destruct cb; cbn.
  reflexivity.
Qed.

Instance Complete_global_decl : CompleteClass global_decl.
Proof.
  unfold CompleteClass, Complete.
  intros l gd.
  destruct gd.
  - cbn -[Deserialize_constant_body].
    rewrite !eqb_ascii_refl.
    rewrite 1!complete_class.
    reflexivity.
  - cbn -[Deserialize_mutual_inductive_body].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite 1!complete_class.
    reflexivity.
Qed.

Instance Complete_global_declarations : CompleteClass global_declarations.
Proof.
  unfold CompleteClass, Complete.
  intros l gd.
  apply complete_class_list.
Qed.



Instance Complete_program : CompleteClass program.
Proof.
  unfold CompleteClass, Complete.
  intros l p.
  apply complete_class.
Qed.
