(** * First-order collapse of the value relation of eta-expansion

    [EEtaExpandSim.eta_value_rel] relates a constructor application to the
    same application with related arguments, or, when the constructor is
    applied to fewer arguments than its declaration asks for, to its
    eta-expansion.  On a first-order value whose constructors are saturated
    ([fo_sat (fo_arity Σ)]) it is therefore equality. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed.
From MetaRocq.Erasure Require EReorderCstrs.
From Peregrine Require Import EFirstOrder EFirstOrderStages EEtaExpand EEtaExpandSim.

Set Default Goal Selector "!".

(** The number of arguments (parameters included) a constructor is declared
    with; [0] for undeclared constructors. *)
Definition fo_arity (Σ : global_declarations) (ind : inductive) (c : nat) : nat :=
  match lookup_constructor_pars_args Σ ind c with
  | Some (p, a) => p + a
  | None => 0
  end.

Lemma value_app_arg' {wfl : WcbvFlags} Σ f a : value Σ (tApp f a) -> value Σ a.
Proof.
  intros H. remember (tApp f a) as t eqn:E.
  destruct H as [? X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
  - exfalso. destruct X as [? i|?]; subst; [cbn in i|]; discriminate.
  - discriminate.
  - destruct (exists_last nn) as (l & x & ->). rewrite mkApps_app in E. cbn in E.
    injection E as <- <-. apply All_app in al as [_ al]. now depelim al.
Qed.

Lemma value_mkApps_args (wfl := default_wcbv_flags) Σ f args : value Σ (mkApps f args) -> All (value Σ) args.
Proof.
  induction args using rev_ind; [constructor|].
  rewrite mkApps_app /=. intros H. apply All_app_inv.
  - apply IHargs. now apply value_tApp_inv in H as [H _].
  - constructor; [|constructor]. eapply value_app_arg'; exact H.
Qed.

Lemma fo_eta_value (wfl := default_wcbv_flags) Σ Σ' v :
  fo_sat (fo_arity Σ) v -> forall v', R Σ Σ' [] v v' -> value Σ' v' -> v' = v.
Proof.
  induction 1 using fo_sat_ind'; intros v' HR Hv.
  - apply R_inv_s in HR; [|reflexivity|reflexivity]. now depelim HR.
  - apply R_inv_s in HR; [|reflexivity|reflexivity].
    destruct p as [? []]; cbn in H; try (now exfalso); now depelim HR.
  - destruct (constr_spine_inv _ _ _ _ _ _ HR Hv) as [(vs' & -> & Hl)|Hp].
    + f_equal. apply Rl_Forall2 in Hl. apply value_mkApps_args in Hv.
      clear -H1 Hl Hv.
      revert H1 Hv. induction Hl; intros H1 Hv; [reflexivity|].
      depelim Hv. inversion H1; subst. f_equal; auto.
    + destruct Hp as (p & a & vs' & j & [-> Hlk Hl Hj [Hlen _]]).
      unfold fo_arity in H. rewrite Hlk in H. lia.
Qed.

Lemma fo_eta_value_rel (wfl := default_wcbv_flags) Σ v v' :
  fo_sat (fo_arity Σ) v -> eta_value_rel Σ v v' -> value (eta_expand_env Σ) v' -> v' = v.
Proof. intros Hs HR Hv. exact (fo_eta_value _ _ _ Hs _ HR Hv). Qed.

(** Eta-expansion does not change the inductives of the environment, hence
    not the data the value translation reads off it. *)
Lemma lookup_minductive_reorder_eta m Σ kn :
  lookup_minductive (EReorderCstrs.reorder_env m (eta_expand_env Σ)) kn =
  lookup_minductive (EReorderCstrs.reorder_env m Σ) kn.
Proof.
  rewrite /lookup_minductive !EReorderCstrs.lookup_env_reorder.
  change (eta_expand_env Σ) with (eta_env_gen Σ Σ). rewrite lookup_env_eta_env_gen.
  destruct (lookup_env Σ kn) as [[]|]; cbn; auto.
Qed.

Lemma fo_npars_reorder_eta m Σ ind :
  fo_npars (EReorderCstrs.reorder_env m (eta_expand_env Σ)) ind =
  fo_npars (EReorderCstrs.reorder_env m Σ) ind.
Proof.
  unfold fo_npars, lookup_inductive_pars. now rewrite lookup_minductive_reorder_eta.
Qed.

Lemma fo_unboxable_reorder_eta m Σ ind c :
  fo_unboxable (EReorderCstrs.reorder_env m (eta_expand_env Σ)) ind c =
  fo_unboxable (EReorderCstrs.reorder_env m Σ) ind c.
Proof.
  unfold fo_unboxable, lookup_constructor, lookup_inductive.
  now rewrite lookup_minductive_reorder_eta.
Qed.
