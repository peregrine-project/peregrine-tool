(** * First-order collapse for the λ□ rewriting passes ([ELboxOpts])

    The observation relation [obs] of the rewriting passes is a chain of
    [R]-steps through arbitrary intermediate terms.  [R] is not syntactic on
    first-order values: it may relate a constructor block to a cofixpoint
    application unfolding to it ([R_cofix]), or to any closed term evaluating
    to a related value ([R_eval]).  The collapse therefore uses

    - a strengthened chain [obsv] recording that every intermediate term is a
      value of its environment (re-proved from [step_pres]);
    - the relation [S] between first-order trees whose leaves may be
      cofixpoint applications: [R] restricted to such a tree on the left and a
      value on the right is contained in [S] ([R_S]);
    - the fact that the final value contains no cofixpoint, which collapses
      the chain backwards to syntactic equality ([obsv_fo]). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed ELiftSubst.
From Peregrine Require Import EFirstOrder EFirstOrderPasses EExtraFlags
  ELboxOptsSimDB ELboxOpts ELboxOptsSim ELboxOptsSimEval ELboxOptsSimStatic ELboxOptsWf.

Set Default Goal Selector "!".
#[local] Set Warnings "-signature-auto-inline".

(** First-order trees up to cofixpoint applications *)
Inductive S : term -> term -> Prop :=
| S_box : S tBox tBox
| S_prim p : fo_prim p -> S (tPrim p) (tPrim p)
| S_construct ind c args args' :
    Forall2 S args args' -> S (tConstruct ind c args) (tConstruct ind c args')
| S_cofix s t : isCoFix (head t) -> S s t.

Lemma S_ind' (P : term -> term -> Prop) :
  P tBox tBox ->
  (forall p, fo_prim p -> P (tPrim p) (tPrim p)) ->
  (forall ind c args args', Forall2 S args args' -> Forall2 P args args' ->
     P (tConstruct ind c args) (tConstruct ind c args')) ->
  (forall s t, isCoFix (head t) -> P s t) ->
  forall s t, S s t -> P s t.
Proof.
  intros Hb Hp Hc Hco.
  fix F 3. intros s t [| p Hprim | ind c args args' Hargs | s' t' H].
  - exact Hb.
  - exact (Hp p Hprim).
  - apply Hc; auto.
    induction Hargs as [|x y l l' Hx Hl IH]; constructor; auto.
  - now apply Hco.
Qed.

Lemma fo_blk_S t : fo_blk t -> S t t.
Proof.
  induction 1 using fo_blk_ind'; try solve [constructor; auto].
  constructor. induction H0; constructor; inversion H; auto.
Qed.

Lemma S_tree_r s t : S s t -> S t t.
Proof.
  induction 1 using S_ind'; try solve [constructor; auto].
  constructor. clear H. induction H0; constructor; auto.
Qed.

(** An [S]-related term that is a block tree collapses onto it. *)
Lemma S_fo_blk s t : fo_blk t -> S s t -> s = t.
Proof.
  intros H; revert s. induction H using fo_blk_ind'; intros s HS.
  - inversion HS; subst; auto. cbn in *. discriminate.
  - inversion HS; subst; auto. cbn in *. discriminate.
  - inversion HS; subst; [|cbn in *; discriminate].
    f_equal.
    match goal with
    | [ HF : Forall2 S _ _ |- _ ] =>
        clear -H0 HF; induction HF; inversion H0; subst; f_equal; auto
    end.
Qed.

(** A cofixpoint-free tree is a first-order value. *)
Lemma S_wf_fo_blk {efl : EEnvFlags} Σ s t :
  has_tApp -> has_tCoFix = false ->
  S s t -> wellformed Σ 0 t -> fo_blk t.
Proof.
  intros Happ Hco. induction 1 using S_ind'; intros Hwf.
  - constructor.
  - now constructor.
  - constructor. cbn in Hwf.
    assert (Hargs : forallb (wellformed Σ 0) args').
    { move: Hwf. destruct cstr_as_blocks; rtoProp; intuition auto.
      destruct args'; cbn in *; auto. }
    clear -H0 Hargs. induction H0; constructor; cbn in Hargs; rtoProp; intuition auto.
  - exfalso. rewrite -(mkApps_head_spine t) wellformed_mkApps // in Hwf.
    destruct (head t); cbn in *; try discriminate.
    rewrite Hco in Hwf. cbn in Hwf. discriminate.
Qed.

Section FO.
  Context {wfl : WcbvFlags}.
  Hypothesis Hblock : with_constructor_as_block = true.
  Hypothesis Hguard : with_guarded_fix = false.
  Hypothesis Hprop : with_prop_case = false.

  (** Shape of values *)
  Lemma value_shape Σ t :
    value Σ t ->
    match t with
    | tBox | tLambda _ _ | tConstruct _ _ _ | tFix _ _ | tCoFix _ _ | tPrim _
    | tLazy _ | tApp _ _ => True
    | _ => False
    end.
  Proof.
    intros [t' Hat|ind c mdecl idecl cdecl args ? ? ? ?|f args Hh Hne Hall]; auto.
    - destruct Hat as [t0 i|]; [destruct t0; cbn in i; auto; try easy|cbn; auto].
    - destruct args using rev_case; [congruence|]. rewrite mkApps_app /= //.
  Qed.

  Ltac kill_src :=
    intros;
    match goal with
    | [ H : S _ _ |- _ ] => inversion H; subst; cbn in *; try discriminate; try contradiction
    end.

  Lemma R_S Σ' :
    (forall s t, R Σ' s t -> forall s0, S s0 s -> value Σ' t -> S s t) /\
    (forall s t, Rh Σ' s t -> forall s0, S s0 s -> value Σ' t -> S s t) /\
    (forall l l', Rs Σ' l l' ->
       Forall (fun a => exists s0, S s0 a) l -> All (value Σ') l' -> Forall2 S l l') /\
    (forall l l', Rbrs Σ' l l' -> True) /\
    (forall l l', Rdefs Σ' l l' -> True).
  Proof.
    apply R_mutind.
    all: try solve [intros; exact I].
    all: try solve [intros; constructor; cbn; auto].
    all: try solve [kill_src].
    - (* R_head *) intros t t' _ IH s0 Hs Hv. eauto.
    - (* R_cofix *) intros. apply S_cofix. now rewrite head_mkApps.
    - (* R_eval *) intros t v0 t' _ IH [ev] _ _ s0 Hs Hv.
      assert (t' = v0) as -> by (eapply eval_value; eassumption). apply (IH s0 Hs).
      eapply eval_to_value; eassumption.
    - (* R_exp *) intros ys s u t' _ IH Hred _ _ s0 Hs Hv.
      destruct ys as [|y ys]; cbn in *.
      + apply value_shape in Hv. destruct Hred; cbn in Hv; contradiction.
      + exfalso.
        assert (Hl : value Σ' (tLambda y (mk_lambdas ys u))) by (now do 2 constructor).
        specialize (IH s0 Hs Hl). inversion IH; subst; cbn in *; discriminate.
    - (* Rh_app *) intros f f' a a' _ _ _ _ s0 Hs Hv.
      apply (value_tApp_inv Hblock Hguard Hprop) in Hv as (mfix & idx & args & -> & _).
      apply S_cofix. now rewrite head_tApp head_mkApps.
    - (* Rh_construct *) intros ind c args args' _ IH s0 Hs Hv.
      constructor. apply IH.
      + inversion Hs; subst; [|cbn in *; discriminate].
        match goal with
        | [ HF : Forall2 S _ args |- _ ] => clear -HF; induction HF; constructor; eauto
        end.
      + now apply value_construct_args in Hv.
    - (* Rh_app_dead *) intros f t0 a' _ _ _ _ _ _ _ s0 Hs Hv.
      apply (value_tApp_inv Hblock Hguard Hprop) in Hv as (mfix & idx & args & -> & _).
      apply S_cofix. now rewrite head_tApp head_mkApps.
    - (* Rs_cons *) intros t t' l l' _ IH _ IHl Hl Hv.
      inversion Hl as [|? ? [s0 Hs0] Hl']; subst. depelim Hv.
      constructor; eauto.
  Qed.

  (** Observation chains through values *)
  Inductive obsv : term -> term -> Prop :=
  | obsv_refl v : obsv v v
  | obsv_step Σ' v v' v'' :
      R Σ' v v' -> ∥ value Σ' v' ∥ -> obsv v' v'' -> obsv v v''.

  (** A chain from a first-order tree to a cofixpoint-free value is trivial. *)
  Lemma obsv_fo v v'' :
    obsv v v'' -> (exists s, S s v) ->
    (forall s, S s v'' -> fo_blk v'') -> v = v''.
  Proof.
    induction 1 as [v|Σ' v v' v'' HR [Hval] Hobs IH]; intros [s Hs] Hfo; auto.
    pose proof (proj1 (R_S Σ') _ _ HR _ Hs Hval) as HS.
    assert (v' = v'') as -> by (apply IH; eauto).
    apply S_fo_blk; eauto.
  Qed.

  Lemma chain_pres_v n : forall Σ Σ' t t' v,
    itr env_step n Σ Σ' -> itr Rall n t t' ->
    closed_env Σ -> pars0 Σ -> closedn 0 t ->
    eval Σ t v ->
    exists v', ∥ eval Σ' t' v' ∥ /\ obsv v v'.
  Proof.
    induction n; cbn; intros Σ Σ' t t' v He Ht Hcl Hp Hct ev.
    - subst. exists v. split; [now sq|constructor].
    - destruct He as (Σ1 & He1 & He), Ht as (t1 & Ht1 & Ht).
      destruct (@step_pres wfl Hblock Hguard Hprop _ _ _ _ _ He1 Ht1 Hcl Hp Hct ev)
        as [(Hcl1 & Hp1 & Hct1) (v1 & [ev1] & Hv1)].
      destruct (IHn _ _ _ _ _ He Ht Hcl1 Hp1 Hct1 ev1) as (v' & ev' & Hv').
      exists v'. split; auto. econstructor; tea.
      sq. eapply eval_to_value; eassumption.
  Qed.

  Variable o : lbox_opts.
  Hypothesis Hnode : forall t, chain t (rewrite_node o t).

  Lemma lbox_opts_program_pres_v (p : program) v :
    closed_env p.1 -> pars0 p.1 -> closedn 0 p.2 ->
    eval p.1 p.2 v ->
    exists v', ∥ eval (lbox_opts_program o p).1 (lbox_opts_program o p).2 v' ∥ /\ obsv v v'.
  Proof.
    intros Hcl Hp Hct ev.
    destruct (@optimize_env_chain wfl o Hnode p.1) as [n Hn].
    destruct (@optimize_chain wfl o Hnode p.2) as [[m Hm] _].
    eapply (chain_pres_v (Nat.max n m)); tea.
    - eapply itr_pad; tea; [apply env_step_refl|lia].
    - eapply itr_pad; tea; [apply Rall_refl|lia].
  Qed.
End FO.

(** ** The collapse lemma at the pipeline's flags *)

Lemma lbox_opts_program_fo (o : lbox_opts) :
  (forall t, chain (wfl := extra_wcbv_flags) t (rewrite_node o t)) ->
  forall (p : program) (v v' : term),
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program o p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program o p) v' ->
  v' = v.
Proof.
  intros Hnode p v v' [wfΣ wft] [wfΣ' wft'] Hfo [ev] [ev'].
  assert (Hpres : exists v1, ∥ eval (wfl := extra_wcbv_flags) (lbox_opts_program o p).1 (lbox_opts_program o p).2 v1 ∥
                         /\ obsv (wfl := extra_wcbv_flags) v v1).
  { refine (lbox_opts_program_pres_v (wfl := extra_wcbv_flags) eq_refl eq_refl eq_refl
              o Hnode p v _ _ _ ev).
    - now eapply wellformed_closed_env.
    - intros kn mdecl.
      now eapply (EImplementBox.wellformed_lookup_inductive_pars (efl := extra_env_flags)).
    - now eapply wellformed_closed. }
  destruct Hpres as (v1 & [ev1] & Hobs).
  rewrite (eval_deterministic ev' ev1). symmetry.
  eapply (obsv_fo (wfl := extra_wcbv_flags) eq_refl eq_refl eq_refl); tea.
  - eexists. now apply fo_blk_S.
  - intros s Hs.
    eapply (S_wf_fo_blk (efl := extra_env_flags)); [reflexivity|reflexivity|exact Hs|].
    eapply (eval_wellformed (efl := extra_env_flags) (wfl := extra_wcbv_flags)); tea.
    reflexivity.
Qed.

Lemma case_id_fo p v v' :
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program case_id_opts p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program case_id_opts p) v' ->
  v' = v.
Proof. apply lbox_opts_program_fo, case_id_node. Qed.

Lemma lbox_opts_fo o p v v' :
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program (without_case_id o) p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program (without_case_id o) p) v' ->
  v' = v.
Proof. apply lbox_opts_program_fo, lbox_node. Qed.
