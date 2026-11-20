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

(** First-order trees up to cofixpoint applications, in either representation
    of constructor applications (blocks or applications) *)
Inductive S : term -> term -> Prop :=
| S_box : S tBox tBox
| S_prim p : fo_prim p -> S (tPrim p) (tPrim p)
| S_construct ind c args args' :
    Forall2 S args args' -> S (tConstruct ind c args) (tConstruct ind c args')
| S_app f f' a a' : S f f' -> S a a' -> S (tApp f a) (tApp f' a')
| S_cofix s t : isCoFix (head t) -> S s t.

Lemma S_ind' (P : term -> term -> Prop) :
  P tBox tBox ->
  (forall p, fo_prim p -> P (tPrim p) (tPrim p)) ->
  (forall ind c args args', Forall2 S args args' -> Forall2 P args args' ->
     P (tConstruct ind c args) (tConstruct ind c args')) ->
  (forall f f' a a', S f f' -> P f f' -> S a a' -> P a a' -> P (tApp f a) (tApp f' a')) ->
  (forall s t, isCoFix (head t) -> P s t) ->
  forall s t, S s t -> P s t.
Proof.
  intros Hb Hp Hc Ha Hco.
  fix F 3. intros s t [| p Hprim | ind c args args' Hargs | f f' a a' Hf Ha' | s' t' H].
  - exact Hb.
  - exact (Hp p Hprim).
  - apply Hc; auto.
    induction Hargs as [|x y l l' Hx Hl IH]; constructor; auto.
  - apply Ha; auto.
  - now apply Hco.
Qed.

Lemma S_mkApps f f' args args' :
  S f f' -> Forall2 S args args' -> S (mkApps f args) (mkApps f' args').
Proof.
  intros Hf Hargs. revert f f' Hf.
  induction Hargs; intros f f' Hf; cbn; auto.
  apply IHHargs. apply S_app; auto.
Qed.

Lemma fo_blk_S t : fo_blk t -> S t t.
Proof.
  induction 1 using fo_blk_ind'; try solve [constructor; auto].
  constructor. induction H0; constructor; inversion H; auto.
Qed.

Lemma fo_app_S t : fo_app t -> S t t.
Proof.
  induction 1 using fo_app_ind'; try solve [constructor; auto].
  apply S_mkApps; [constructor; constructor|].
  clear H. induction H0; constructor; auto.
Qed.

(** A cofixpoint-free related tree is equal. *)
Lemma S_wf_eq {efl : EEnvFlags} Σ s t :
  has_tApp -> has_tCoFix = false ->
  S s t -> wellformed Σ 0 t -> s = t.
Proof.
  intros Happ Hco. induction 1 using S_ind'; intros Hwf; auto.
  - f_equal. cbn in Hwf.
    assert (Hargs : forallb (wellformed Σ 0) args').
    { move: Hwf. destruct cstr_as_blocks; rtoProp; intuition auto.
      destruct args'; cbn in *; auto. }
    clear -H0 Hargs. induction H0; cbn in Hargs; rtoProp; f_equal; intuition auto.
  - cbn in Hwf. rtoProp. f_equal; intuition auto.
  - exfalso. rewrite -(mkApps_head_spine t) wellformed_mkApps // in Hwf.
    destruct (head t); cbn in *; try discriminate.
    rewrite Hco in Hwf. cbn in Hwf. discriminate.
Qed.

Lemma S_head s t : S s t ->
  match head t with
  | tBox | tPrim _ | tConstruct _ _ _ | tCoFix _ _ => True
  | _ => False
  end.
Proof.
  induction 1 using S_ind'; rewrite ?head_tApp; auto; try exact I.
  destruct (head t); cbn in *; auto; discriminate.
Qed.

Lemma dead_head_shape f : dead_head f ->
  match head f with tLambda _ _ | tFix _ _ => True | _ => False end.
Proof.
  intros [(na & d & ->)|(mf & idx & cs & -> & _)]; rewrite ?head_mkApps; exact I.
Qed.

Section FO.
  Context {wfl : WcbvFlags}.
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

  Lemma value_app_arg Σ f a : value Σ (tApp f a) -> value Σ a.
  Proof.
    intros H. remember (tApp f a) as t eqn:E.
    destruct H as [? X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
    - exfalso. destruct X as [? i|?]; subst; [cbn in i|]; discriminate.
    - discriminate.
    - destruct (exists_last nn) as (l & x & ->). rewrite mkApps_app in E. cbn in E.
      injection E as <- <-. apply All_app in al as [_ al]. now depelim al.
  Qed.

  (** [R] at a target value: cofixpoint applications are related to
      cofixpoint applications only, and trees to trees. *)
  Definition PS Σ' (s t : term) : Prop :=
    value Σ' t ->
    (isCoFix (head s) -> isCoFix (head t)) /\ (forall s0, S s0 s -> S s t).

  Lemma PS_cofix Σ' s t : isCoFix (head t) -> PS Σ' s t.
  Proof. intros H Hv; split; intros; [exact H|now apply S_cofix]. Qed.

  Ltac triv :=
    unfold PS; intros; split;
    [rewrite ?head_tApp; cbn; intros Hc; discriminate Hc
    |intros s0 Hs0; exfalso; apply S_head in Hs0; rewrite ?head_tApp in Hs0; exact Hs0].

  Ltac leaf :=
    unfold PS; intros; split;
    [rewrite ?head_tApp; cbn; intros Hc; solve [discriminate Hc|exact Hc]
    |intros s0 Hs0; inversion Hs0; subst; cbn in *; try discriminate; try contradiction;
     solve [constructor; auto|apply S_cofix; reflexivity]].

  Lemma R_S Σ' :
    (forall s t, R Σ' s t -> PS Σ' s t) /\
    (forall s t, Rh Σ' s t -> PS Σ' s t) /\
    (forall l l', Rs Σ' l l' ->
       Forall (fun a => exists s0, S s0 a) l -> All (value Σ') l' -> Forall2 S l l') /\
    (forall l l', Rbrs Σ' l l' -> True) /\
    (forall l l', Rdefs Σ' l l' -> True).
  Proof.
    apply R_mutind.
    all: try solve [intros; exact I].
    all: try solve [intros; assumption].
    all: try solve [triv].
    all: try solve [leaf].
    all: try solve [intros; constructor].
    - (* R_cofix *) intros. apply PS_cofix. now rewrite head_mkApps.
    - (* R_eval *) intros t v0 t' _ IH [ev] _ _ Hv.
      assert (t' = v0) as -> by (eapply eval_value; eassumption). exact (IH Hv).
    - (* R_exp *) intros ys s u t' _ IH Hred _ _ Hv.
      destruct ys as [|y ys]; cbn in *.
      + apply value_shape in Hv. destruct Hred; cbn in Hv; contradiction.
      + assert (Hl : value Σ' (tLambda y (mk_lambdas ys u))) by (now do 2 constructor).
        destruct (IH Hl) as [H1 H2]. split.
        * intros Hc. specialize (H1 Hc). cbn in H1. discriminate.
        * intros s0 Hs0. specialize (H2 _ Hs0). apply S_head in H2. destruct H2.
    - (* Rh_app *) intros f f' a a' _ IHf _ IHa Hv.
      destruct (IHf (value_app_head Hguard _ _ _ Hv)) as [F1 F2].
      destruct (IHa (value_app_arg _ _ _ Hv)) as [_ A2].
      split; [rewrite !head_tApp; exact F1|].
      intros s0 Hs0. destruct (isCoFix (head f)) eqn:Hc.
      + apply S_cofix. rewrite head_tApp. now apply F1.
      + inversion Hs0; subst; [apply S_app; eauto|].
        match goal with
        | [ H : is_true (isCoFix _) |- _ ] => rewrite head_tApp Hc in H; discriminate H
        end.
    - (* Rh_construct *) intros ind c args args' _ IH Hv.
      split; [cbn; intros Hc; discriminate Hc|]. intros s0 Hs0.
      constructor. apply IH.
      + inversion Hs0; subst; [|cbn in *; discriminate].
        match goal with
        | [ HF : Forall2 S _ args |- _ ] => clear -HF; induction HF; constructor; eauto
        end.
      + now apply value_construct_args in Hv.
    - (* Rh_app_dead *) intros f t0 a' _ _ Hd _ _ _ _ Hv.
      apply dead_head_shape in Hd. split.
      + rewrite !head_tApp. intros Hc. exfalso. revert Hc Hd.
        destruct (head f); cbn; intros; try discriminate; contradiction.
      + intros s0 Hs0. exfalso. apply S_head in Hs0. rewrite head_tApp in Hs0.
        revert Hs0 Hd. destruct (head f); cbn; intros; contradiction.
    - (* Rs_cons *) intros t t' l l' _ IH _ IHl Hl Hv.
      inversion Hl as [|? ? [s0 Hs0] Hl']; subst. depelim Hv.
      constructor; [|now eauto]. destruct (IH v) as [_ H2]. eauto.
  Qed.

  (** Observation chains through values *)
  Inductive obsv : term -> term -> Prop :=
  | obsv_refl v : obsv v v
  | obsv_step Σ' v v' v'' :
      R Σ' v v' -> ∥ value Σ' v' ∥ -> obsv v' v'' -> obsv v v''.

  (** A chain from a first-order tree to a cofixpoint-free value is trivial. *)
  Lemma obsv_fo v v'' :
    obsv v v'' -> (exists s, S s v) ->
    (forall s, S s v'' -> s = v'') -> v = v''.
  Proof.
    induction 1 as [v|Σ' v v' v'' HR [Hval] Hobs IH]; intros [s Hs] Hfo; auto.
    pose proof (proj2 (proj1 (R_S Σ') _ _ HR Hval) _ Hs) as HS.
    assert (v' = v'') as -> by (apply IH; eauto).
    now apply Hfo.
  Qed.

  Lemma chain_pres_v n : forall Σ Σ' t t' v,
    itr env_step n Σ Σ' -> itr Rall n t t' ->
    closed_env Σ -> closedn 0 t ->
    eval Σ t v ->
    exists v', ∥ eval Σ' t' v' ∥ /\ obsv v v'.
  Proof.
    induction n; cbn; intros Σ Σ' t t' v He Ht Hcl Hct ev.
    - subst. exists v. split; [now sq|constructor].
    - destruct He as (Σ1 & He1 & He), Ht as (t1 & Ht1 & Ht).
      destruct (step_pres Hguard Hprop _ _ _ _ _ He1 Ht1 Hcl Hct ev)
        as [(Hcl1 & Hct1) (v1 & [ev1] & Hv1)].
      destruct (IHn _ _ _ _ _ He Ht Hcl1 Hct1 ev1) as (v' & ev' & Hv').
      exists v'. split; auto. econstructor; tea.
      sq. eapply eval_to_value; eassumption.
  Qed.

  Variable o : lbox_opts.
  Hypothesis Hnode : forall t, chain t (rewrite_node o t).

  Lemma lbox_opts_program_pres_v (p : program) v :
    closed_env p.1 -> closedn 0 p.2 ->
    eval p.1 p.2 v ->
    exists v', ∥ eval (lbox_opts_program o p).1 (lbox_opts_program o p).2 v' ∥ /\ obsv v v'.
  Proof.
    intros Hcl Hct ev.
    destruct (optimize_env_chain o Hnode p.1) as [n Hn].
    destruct (optimize_chain o Hnode p.2) as [[m Hm] _].
    eapply (chain_pres_v (Nat.max n m)); tea.
    - eapply itr_pad; tea; [apply env_step_refl|lia].
    - eapply itr_pad; tea; [apply Rall_refl|lia].
  Qed.
End FO.

(** ** The collapse lemma, for any flags *)

Lemma lbox_opts_program_fo_gen {wfl : WcbvFlags} {efl : EEnvFlags} (o : lbox_opts) :
  with_guarded_fix = false -> with_prop_case = false ->
  has_tApp -> has_tCoFix = false ->
  (forall t, chain t (rewrite_node o t)) ->
  forall (p : program) (v v' : term),
  wf_eprogram efl p ->
  wf_eprogram efl (lbox_opts_program o p) ->
  (exists s, S s v) ->
  eval_eprogram wfl p v ->
  eval_eprogram wfl (lbox_opts_program o p) v' ->
  v' = v.
Proof.
  intros Hguard Hprop Happ Hco Hnode p v v' [wfΣ wft] [wfΣ' wft'] Hfo [ev] [ev'].
  assert (Hpres : exists v1, ∥ eval (lbox_opts_program o p).1 (lbox_opts_program o p).2 v1 ∥
                         /\ obsv v v1).
  { refine (lbox_opts_program_pres_v Hguard Hprop o Hnode p v _ _ ev).
    - now eapply wellformed_closed_env.
    - now eapply wellformed_closed. }
  destruct Hpres as (v1 & [ev1] & Hobs).
  rewrite (eval_deterministic ev' ev1). symmetry.
  eapply (obsv_fo Hguard); tea.
  intros s Hs.
  eapply (S_wf_eq (efl := efl)); [exact Happ|exact Hco|exact Hs|].
  eapply (eval_wellformed (efl := efl)); tea.
Qed.

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
  intros Hnode p v v' wf wf' Hfo ev ev'.
  refine (lbox_opts_program_fo_gen (wfl := extra_wcbv_flags) (efl := extra_env_flags) o
            eq_refl eq_refl eq_refl eq_refl Hnode p v v' wf wf' _ ev ev').
  eexists. now apply fo_blk_S.
Qed.

Lemma case_id_fo p v v' :
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program case_id_opts p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program case_id_opts p) v' ->
  v' = v.
Proof. apply lbox_opts_program_fo, case_id_node. Qed.

Lemma iota_fo p v v' :
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program iota_opts p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program iota_opts p) v' ->
  v' = v.
Proof. apply lbox_opts_program_fo, lbox_node. Qed.

Lemma lbox_opts_fo o p v v' :
  wf_eprogram extra_env_flags p ->
  wf_eprogram extra_env_flags (lbox_opts_program (without_case_id o) p) ->
  fo_blk v ->
  eval_eprogram extra_wcbv_flags p v ->
  eval_eprogram extra_wcbv_flags (lbox_opts_program (without_case_id o) p) v' ->
  v' = v.
Proof. apply lbox_opts_program_fo, lbox_node. Qed.
