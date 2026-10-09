(** * EHindleyMilnerSound: scoping of the [box_type] annotations emitted by
      [EHindleyMilner.infer].

    Proved (all [Qed]):
    - every constant scheme emitted by [infer] is CLOSED: each [TVar n] in its
      body is bound by its quantifier list ([n < #|vars|]), hence every scheme
      in the table is INSTANTIABLE ([instantiate base] lands all variables in
      the fresh region [[base, base + #|vars|)]);
    - inductive bodies emitted by [infer] carry no type variables;
    - consequently the Rust/Elm printers' [print_type], which resolves [TVar n]
      by [nth_error] in a context built from the quantifier list, never hits
      its "unbound TVar" failure on inferred types ([infer_tvars_resolve]).

    NOT proved here, and false for the current algorithm: that the annotations
    are coherent enough for the printed Rust/Elm to type-check (the [tCase]
    scrutinee is left unconstrained, inductive bodies get [TAny] fields and
    lack the [ind_npars] parameter entries). *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From Peregrine Require Import EHindleyMilner.

Import ListNotations.

Definition tvars_lt (k : nat) (t : ExAst.box_type) : Prop :=
  forall n, In n (ftv t) -> n < k.

Definition scheme_closed (sch : scheme) : Prop :=
  tvars_lt (length (fst sch)) (snd sch).

(** ** Generalization produces closed schemes *)

Lemma mem_nat_In n l : mem_nat n l = true <-> In n l.
Proof.
  induction l as [|m l IH]; cbn.
  - split; [discriminate|tauto].
  - destruct (Nat.eqb_spec n m) as [->|Hne].
    + split; intros _; [left; reflexivity|reflexivity].
    + rewrite IH. split; [tauto|]. intros [H|H]; [congruence|exact H].
Qed.

Lemma dedup_nat_In n l : In n (dedup_nat l) <-> In n l.
Proof.
  induction l as [|m l IH]; cbn; [tauto|].
  destruct (mem_nat m (dedup_nat l)) eqn:Hm.
  - apply mem_nat_In in Hm. rewrite IH. split; [tauto|].
    intros [->|H]; [apply IH, Hm|exact H].
  - cbn. rewrite IH. tauto.
Qed.

Lemma idx_nat_lt n l : In n l -> idx_nat n l < length l.
Proof.
  induction l as [|m l IH]; cbn; [tauto|].
  destruct (Nat.eqb_spec n m) as [->|Hne]; [lia|].
  intros [H|H]; [congruence|]. specialize (IH H). lia.
Qed.

Lemma ftv_rename_tv vs t m :
  In m (ftv (rename_tv vs t)) -> exists n, In n (ftv t) /\ m = idx_nat n vs.
Proof.
  induction t as [| |a IHa b IHb|a IHa b IHb|k| |]; cbn; intros H; try contradiction.
  - apply in_app_iff in H. destruct H as [H|H].
    + apply IHa in H as (n & Hn & ->). exists n. split; [apply in_app_iff; auto|reflexivity].
    + apply IHb in H as (n & Hn & ->). exists n. split; [apply in_app_iff; auto|reflexivity].
  - apply in_app_iff in H. destruct H as [H|H].
    + apply IHa in H as (n & Hn & ->). exists n. split; [apply in_app_iff; auto|reflexivity].
    + apply IHb in H as (n & Hn & ->). exists n. split; [apply in_app_iff; auto|reflexivity].
  - destruct H as [<-|[]]. exists k. split; [left|]; reflexivity.
Qed.

Lemma generalize_ty_closed t : scheme_closed (generalize_ty t).
Proof.
  unfold scheme_closed, tvars_lt, generalize_ty; cbn. intros m Hm.
  rewrite length_map.
  apply ftv_rename_tv in Hm as (n & Hn & ->).
  apply idx_nat_lt, dedup_nat_In, Hn.
Qed.

Lemma infer_cst_type_closed D E b : scheme_closed (infer_cst_type D E b).
Proof.
  unfold infer_cst_type. destruct b as [t|]; [|intros n []].
  destruct (infer_tm infer_fuel D E [] 0 [] t) as [[ty s] c].
  apply generalize_ty_closed.
Qed.

(** ** Closed schemes instantiate into the fresh region *)

Lemma ftv_inst_tv base t : ftv (inst_tv base t) = map (Nat.add base) (ftv t).
Proof.
  induction t; cbn; try reflexivity; rewrite map_app; congruence.
Qed.

Lemma instantiate_fresh base sch :
  scheme_closed sch ->
  forall n, In n (ftv (fst (instantiate base sch))) ->
            base <= n < snd (instantiate base sch).
Proof.
  destruct sch as [vs body]; unfold scheme_closed, tvars_lt; cbn; intros Hc n Hn.
  rewrite ftv_inst_tv in Hn. apply in_map_iff in Hn as (k & <- & Hk).
  specialize (Hc k Hk). lia.
Qed.

(** ** Inductive bodies carry no type variables *)

Definition oib_no_tvars (oib : ExAst.one_inductive_body) : Prop :=
  Forall (fun '(_, args, _) => Forall (fun '(_, ty) => ftv ty = []) args)
         oib.(ExAst.ind_ctors)
  /\ Forall (fun '(_, ty) => ftv ty = []) oib.(ExAst.ind_projs).

Lemma infer_oib_no_tvars oib : oib_no_tvars (infer_oib oib).
Proof.
  unfold oib_no_tvars, infer_oib; cbn. split; apply Forall_map, Forall_forall.
  - intros c _. apply Forall_forall. intros [na ty] Hin.
    apply repeat_spec in Hin. now inversion Hin.
  - intros p _. reflexivity.
Qed.

(** ** The whole emitted environment *)

Definition decl_scoped (d : ExAst.global_decl) : Prop :=
  match d with
  | ExAst.ConstantDecl cb => scheme_closed cb.(ExAst.cst_type)
  | ExAst.InductiveDecl mib => Forall oib_no_tvars mib.(ExAst.ind_bodies)
  | ExAst.TypeAliasDecl _ => False (* never emitted *)
  end.

Lemma infer_const_scoped D E cb : decl_scoped (ExAst.ConstantDecl (infer_const D E cb)).
Proof. exact (infer_cst_type_closed D E cb.(EAst.cst_body)). Qed.

Lemma infer_mib_scoped mib : decl_scoped (ExAst.InductiveDecl (infer_mib mib)).
Proof.
  cbn [decl_scoped infer_mib ExAst.ind_bodies].
  apply Forall_map, Forall_forall. intros o _. apply infer_oib_no_tvars.
Qed.

Lemma infer_go_scoped D Σ :
  Forall (fun '(_, _, d) => decl_scoped d) (fst (infer_go D Σ))
  /\ Forall (fun '(_, sch) => scheme_closed sch) (snd (infer_go D Σ)).
Proof.
  induction Σ as [|[kn d] Σ IH]; [split; constructor|].
  simpl infer_go. destruct (infer_go D Σ) as [env E].
  destruct IH as [Henv HE]; cbn [fst snd] in Henv, HE.
  destruct d as [cb|mib]; cbn [fst snd].
  - split; constructor; [exact (infer_const_scoped D E cb)|exact Henv|
                         exact (infer_cst_type_closed D E cb.(EAst.cst_body))|exact HE].
  - split; [constructor; [exact (infer_mib_scoped mib)|exact Henv]|exact HE].
Qed.

Theorem infer_scoped D Σ : Forall (fun '(_, _, d) => decl_scoped d) (infer D Σ).
Proof. exact (proj1 (infer_go_scoped D Σ)). Qed.

(** The Rust/Elm printers resolve [TVar n] by [nth_error] in a context built
    from the scheme's quantifier list ([print_constant]); on inferred schemes
    this lookup never fails. *)
Corollary infer_tvars_resolve D Σ kn b cb {A} (Γ : list A) :
  In (kn, b, ExAst.ConstantDecl cb) (infer D Σ) ->
  length Γ = length (fst cb.(ExAst.cst_type)) ->
  forall n, In n (ftv (snd cb.(ExAst.cst_type))) -> nth_error Γ n <> None.
Proof.
  intros Hin HΓ n Hn.
  pose proof (proj1 (Forall_forall _ _) (infer_scoped D Σ) _ Hin) as Hc.
  apply nth_error_Some. rewrite HΓ. apply Hc, Hn.
Qed.

Print Assumptions infer_scoped.
Print Assumptions infer_tvars_resolve.
Print Assumptions instantiate_fresh.
