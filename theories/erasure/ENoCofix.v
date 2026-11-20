(** * Programs without cofixpoints

    Peregrine rejects cofixpoints up front ([check_wf], Pipeline.v) and runs
    the middle-end at [nocofix_env_flags] (EExtraFlags.v).  MetaRocq's
    dearging pass (Typed/OptimizeCorrectness.v) is proved wellformedness
    preserving at [all_env_flags] only.  This file relates wellformedness at
    the two flags: wellformed at [nocofix_env_flags] is wellformed at
    [all_env_flags] and free of [tCoFix] ([no_cofix]), and dearging does not
    introduce cofixpoints, so it preserves wellformedness at
    [nocofix_env_flags] as well. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst EWellformed EGlobalEnv EPrimitive EProgram.
From MetaRocq.Erasure.Typed Require ExAst Optimize OptimizeCorrectness.
From Peregrine Require Import EExtraFlags.

Fixpoint no_cofix (t : term) : bool :=
  match t with
  | tRel _ | tVar _ | tBox | tConst _ => true
  | tEvar _ args => forallb no_cofix args
  | tLambda _ b => no_cofix b
  | tLetIn _ b b' => no_cofix b && no_cofix b'
  | tApp u v => no_cofix u && no_cofix v
  | tConstruct _ _ args => forallb no_cofix args
  | tCase _ c brs => no_cofix c && forallb (fun br => no_cofix br.2) brs
  | tProj _ c => no_cofix c
  | tFix mfix _ => forallb (fun d => no_cofix d.(dbody)) mfix
  | tCoFix _ _ => false
  | tPrim p => test_prim no_cofix p
  | tLazy t | tForce t => no_cofix t
  end.

Definition glob_no_cofix (Σ : global_declarations) : bool :=
  forallb (fun d => match d.2 with
                    | ConstantDecl cb => option_default no_cofix cb.(cst_body) true
                    | InductiveDecl _ => true
                    end) Σ.

Ltac nocofix_crush :=
  repeat (
    cbn in * ||
    unfold wf_fix_gen, test_def, test_prim, test_array_model in * ||
    match goal with
    | X : primProp _ _ |- _ => inversion X as [| | | ? [? ?]]; subst; clear X
    | |- _ -> _ => intro
    | h : _ /\ _ |- _ => destruct h
    | h : is_true (_ && _) |- _ => apply andb_and in h
    | h : is_true (is_nil ?l) |- _ => destruct l; [clear h|discriminate h]
    end); rtoProp; intuition auto; solve_all.

Section Flags.
  Context (Σ : global_context).

  Lemma wellformed_nocofix_all k t :
    wellformed (efl := nocofix_env_flags) Σ k t ->
    wellformed (efl := all_env_flags) Σ k t.
  Proof.
    induction t using term_forall_list_ind in k |- *; nocofix_crush.
  Qed.

  Lemma wellformed_nocofix_no_cofix k t :
    wellformed (efl := nocofix_env_flags) Σ k t -> no_cofix t.
  Proof.
    induction t using term_forall_list_ind in k |- *; nocofix_crush.
  Qed.

  Lemma wellformed_all_nocofix k t :
    wellformed (efl := all_env_flags) Σ k t -> no_cofix t ->
    wellformed (efl := nocofix_env_flags) Σ k t.
  Proof.
    induction t using term_forall_list_ind in k |- *; nocofix_crush.
  Qed.
End Flags.

Lemma wf_glob_nocofix Σ :
  wf_glob (efl := nocofix_env_flags) Σ <->
  wf_glob (efl := all_env_flags) Σ /\ glob_no_cofix Σ.
Proof.
  induction Σ as [|[kn d] Σ IH].
  - split; [split; [constructor|reflexivity]|constructor].
  - split.
    + intros h; depelim h. apply IH in h as [? ?].
      split; [constructor; auto|].
      * destruct d as [[[b|]]|]; cbn in *; auto.
        now eapply wellformed_nocofix_all.
      * cbn. rtoProp; split; auto.
        destruct d as [[[b|]]|]; cbn in *; auto.
        now eapply wellformed_nocofix_no_cofix.
    + intros [h hc]; depelim h. cbn in hc; rtoProp.
      constructor; auto.
      * apply IH; split; auto.
      * destruct d as [[[b|]]|]; cbn in *; auto.
        now eapply wellformed_all_nocofix.
Qed.

Lemma wf_eprogram_nocofix (p : eprogram) :
  wf_eprogram nocofix_env_flags p <->
  wf_eprogram all_env_flags p /\ glob_no_cofix p.1 /\ no_cofix p.2.
Proof.
  destruct p as [Σ t]; cbn.
  rewrite /wf_eprogram /= wf_glob_nocofix.
  intuition auto.
  - now eapply wellformed_nocofix_all.
  - now eapply wellformed_nocofix_no_cofix.
  - now eapply wellformed_all_nocofix.
Qed.

(** ** Cofixpoint-freeness is preserved by substitution and dearging *)

Lemma forallb_map_eq {A B} (f : B -> bool) (g : A -> B) (h : A -> bool) l :
  All (fun x => f (g x) = h x) l -> forallb f (map g l) = forallb h l.
Proof. induction 1; cbn; congruence. Qed.

Lemma no_cofix_lift n k t : no_cofix (lift n k t) = no_cofix t.
Proof.
  induction t using term_forall_list_ind in k |- *; cbn; auto.
  all: try (destruct Nat.leb; reflexivity).
  all: rewrite ?IHt ?IHt1 ?IHt2; try reflexivity.
  all: try (apply forallb_map_eq; eapply All_impl; tea; cbn; intros; eauto; fail).
  - f_equal. apply forallb_map_eq; eapply All_impl; tea; cbn; intros; eauto.
  - destruct p as [? []]; cbn in *; depelim X; auto.
    destruct p; unfold test_array_model; cbn in *. rewrite e. f_equal.
    apply forallb_map_eq; eapply All_impl; tea; cbn; intros; eauto.
Qed.

Lemma no_cofix_subst s k t :
  forallb no_cofix s -> no_cofix t -> no_cofix (subst s k t).
Proof.
  intros hs.
  induction t using term_forall_list_ind in k |- *; cbn; auto; intros; rtoProp;
    rewrite ?forallb_map; try solve [intuition auto; solve_all].
  - destruct Nat.leb => //. destruct nth_error eqn:hnth => //.
    rewrite no_cofix_lift. eapply nth_error_forallb in hnth; tea.
  - destruct p as [? []]; cbn in *; depelim X; auto.
    destruct p; unfold test_array_model in *; cbn in *. rtoProp; split; eauto.
    rewrite forallb_map. solve_all.
Qed.

Lemma no_cofix_mkApps f args :
  no_cofix (mkApps f args) = no_cofix f && forallb no_cofix args.
Proof.
  induction args in f |- *; cbn; [now rewrite andb_true_r|].
  rewrite IHargs /=. now rewrite andb_assoc.
Qed.

Section Dearg.
  Import Optimize.
  Context (ind_masks : list (Kernames.kername * mib_masks)).
  Context (const_masks : list (Kernames.kername * bitmask)).

  Lemma no_cofix_dearg_single mask t args :
    no_cofix t -> forallb no_cofix args ->
    no_cofix (dearg_single mask t args).
  Proof.
    induction mask as [|b mask IH] in t, args |- *; intros ht hargs.
    - cbn. destruct args; rewrite no_cofix_mkApps; rtoProp; auto.
    - destruct b, args as [|a args]; cbn in *; rtoProp.
      all: apply IH; cbn; rewrite ?no_cofix_lift; rtoProp; auto.
  Qed.

  Lemma no_cofix_dearg_lambdas mask t :
    no_cofix t -> no_cofix (dearg_lambdas mask t).
  Proof.
    induction t in mask |- *; cbn; auto; intros; rtoProp.
    - destruct mask as [|[] mask]; cbn; auto.
      apply no_cofix_subst; cbn; auto.
    - split; auto.
  Qed.

  Lemma no_cofix_dearg_branch_body_rec i mask t :
    no_cofix t -> no_cofix (dearg_branch_body_rec i mask t).2.
  Proof.
    unfold dearg_branch_body_rec.
    induction mask as [|[] mask IH] in i, t |- *; cbn; auto; intros.
    apply IH. now apply no_cofix_subst.
  Qed.

  Lemma no_cofix_dearg_case_branches mm ind brs :
    forallb (fun br => no_cofix br.2) brs ->
    forallb (fun br => no_cofix br.2) (dearg_case_branches mm ind brs).
  Proof.
    destruct mm as [mm|]; cbn; auto.
    unfold mapi. generalize 0 as n.
    induction brs as [|br brs IH]; intros n; cbn; auto; intros; rtoProp.
    split; auto.
    unfold dearg_case_branch. destruct Nat.leb; cbn; auto.
    now apply no_cofix_dearg_branch_body_rec.
  Qed.

  Lemma no_cofix_dearg_aux args t :
    no_cofix t -> forallb no_cofix args ->
    no_cofix (dearg_aux ind_masks const_masks args t).
  Proof.
    induction t using term_forall_list_ind in args |- *; cbn; intros ht hargs; rtoProp.
    all: try (rewrite no_cofix_mkApps; cbn; rtoProp; intuition auto; rewrite ?forallb_map; solve_all; fail).
    - apply IHt1; cbn; rtoProp; auto.
    - now apply no_cofix_dearg_single.
    - now apply no_cofix_dearg_single.
    - destruct p as [ind npars]. rewrite no_cofix_mkApps; cbn; rtoProp; intuition auto.
      apply no_cofix_dearg_case_branches. rewrite forallb_map. cbn. solve_all.
    - destruct s as [ind npars arg]. rewrite no_cofix_mkApps; cbn; rtoProp; intuition auto.
    - rewrite no_cofix_mkApps; cbn; rtoProp; split; auto.
      destruct p as [? []]; cbn in *; depelim X; auto.
      destruct p; unfold test_array_model in *; cbn in *; rtoProp; split; eauto.
      rewrite forallb_map. solve_all.
  Qed.

  Lemma no_cofix_dearg t : no_cofix t -> no_cofix (dearg ind_masks const_masks t).
  Proof. intros. now apply no_cofix_dearg_aux. Qed.

  Lemma glob_no_cofix_dearg_env Σ :
    glob_no_cofix (ExAst.trans_env Σ) ->
    glob_no_cofix (ExAst.trans_env (dearg_env ind_masks const_masks Σ)).
  Proof.
    induction Σ as [|[[kn b] d] Σ IH]; cbn; auto; intros; rtoProp.
    split; auto.
    destruct d as [[ty [body|]]| |]; cbn in *; auto.
    apply no_cofix_dearg, no_cofix_dearg_lambdas; auto.
  Qed.
End Dearg.

Lemma glob_no_cofix_dearg_env' masks Σ :
  glob_no_cofix (ExAst.trans_env Σ) ->
  glob_no_cofix (ExAst.trans_env (OptimizeCorrectness.dearg_env masks Σ)).
Proof.
  intros h. rewrite /OptimizeCorrectness.dearg_env -OptimizeCorrectness.trans_env_debox.
  now apply glob_no_cofix_dearg_env.
Qed.
