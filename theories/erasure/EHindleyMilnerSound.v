(** * EHindleyMilnerSound: scoping of the [box_type] annotations emitted by
      [EHindleyMilner.infer].

    Proved (all [Qed]), for every environment [Σ'] with [infer Σ = Ok Σ']:
    - every constant scheme in [Σ'] is CLOSED: each [TVar n] in its body is
      bound by its quantifier list ([n < #|vars|]) — [infer_scoped];
    - every type variable in a constructor field or projection type of an
      inductive body of [Σ'] is below the number of its [ind_type_vars]
      — [infer_scoped];
    - consequently the Rust/Elm printers' [print_type], which resolves
      [TVar n] by [nth_error] in a context built from the quantifier list
      (resp. the type-variable list), never hits its "unbound TVar" failure
      on inferred types — [infer_tvars_resolve];
    - [instantiate] renames exactly the bound variables of a scheme into the
      fresh region [[base, base + #|vars|)] and leaves its free (global)
      variables alone — [instantiate_vars], [instantiate_fresh].

    These are properties of the EMISSION step ([emit_scheme], [emit_field]):
    bound variables are renamed to their index and every other variable
    becomes [TBox].  NOT proved: that the annotations describe the terms (no
    typing judgement for λ□ᵀ exists yet), nor anything about the pending
    constraint resolution beyond what emission guarantees. *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From Peregrine Require Import EHindleyMilner.

Import ListNotations.

Definition tvars_lt (k : nat) (t : ExAst.box_type) : Prop :=
  forall n, In n (ftv t) -> n < k.

Definition scheme_closed (sch : list name * ExAst.box_type) : Prop :=
  tvars_lt (length (fst sch)) (snd sch).

(** ** Emission renames bound variables to indices and boxes the rest *)

Lemma mem_nat_In n l : mem_nat n l = true <-> In n l.
Proof.
  induction l as [|m l IH]; cbn.
  - split; [discriminate|tauto].
  - destruct (Nat.eqb_spec n m) as [->|Hne].
    + split; intros _; [left; reflexivity|reflexivity].
    + rewrite IH. split; [tauto|]. intros [H|H]; [congruence|exact H].
Qed.

Lemma idx_nat_lt n l : In n l -> idx_nat n l < length l.
Proof.
  induction l as [|m l IH]; cbn; [tauto|].
  destruct (Nat.eqb_spec n m) as [->|Hne]; [lia|].
  intros [H|H]; [congruence|]. specialize (IH H). lia.
Qed.

Lemma rename_or_box_lt vs t : tvars_lt (length vs) (rename_or_box vs t).
Proof.
  unfold tvars_lt.
  induction t as [| |a IHa b IHb|a IHa b IHb|k| |]; cbn; intros n Hn; try contradiction.
  - apply in_app_iff in Hn. destruct Hn; auto.
  - apply in_app_iff in Hn. destruct Hn; auto.
  - destruct (mem_nat k vs) eqn:Hm; cbn in Hn; [|contradiction].
    destruct Hn as [<-|[]]. apply idx_nat_lt, mem_nat_In, Hm.
Qed.

Lemma emit_scheme_closed sch : scheme_closed (emit_scheme sch).
Proof.
  destruct sch as [vs body]. unfold scheme_closed, emit_scheme; cbn.
  rewrite length_map. apply rename_or_box_lt.
Qed.

Lemma emit_field_lt params f : tvars_lt (length params) (emit_field params f).
Proof. destruct f; cbn; [apply rename_or_box_lt|intros n []]. Qed.

(** ** Inductive bodies: fields and projections are scoped by [ind_type_vars] *)

Definition oib_scoped (oib : ExAst.one_inductive_body) : Prop :=
  let k := length oib.(ExAst.ind_type_vars) in
  Forall (fun '(_, args, _) => Forall (fun '(_, ty) => tvars_lt k ty) args) oib.(ExAst.ind_ctors)
  /\ Forall (fun '(_, ty) => tvars_lt k ty) oib.(ExAst.ind_projs).

Lemma emit_oib_aux_scoped params ctors oib : oib_scoped (emit_oib_aux params ctors oib).
Proof.
  unfold oib_scoped, emit_oib_aux, mapi; cbn. rewrite length_map. split.
  - generalize 0 as k. induction (EAst.ind_ctors oib) as [|c cs IH]; intros k; cbn; constructor; [|apply IH].
    unfold emit_ctor. apply (proj2 (List.Forall_app _ _ _)). split.
    + apply Forall_forall. intros [na ty] Hin. apply repeat_spec in Hin.
      injection Hin as -> ->. intros n [].
    + apply Forall_map, Forall_forall. intros f _. apply emit_field_lt.
  - generalize 0 as k. induction (EAst.ind_projs oib) as [|p ps IH]; intros k; cbn; constructor; [|apply IH].
    apply emit_field_lt.
Qed.

Lemma emit_oib_scoped T kn i oib : oib_scoped (emit_oib T kn i oib).
Proof. unfold emit_oib. destruct (sig_lookup T kn); apply emit_oib_aux_scoped. Qed.

(** ** The whole emitted environment *)

Definition decl_scoped (d : ExAst.global_decl) : Prop :=
  match d with
  | ExAst.ConstantDecl cb => scheme_closed cb.(ExAst.cst_type)
  | ExAst.InductiveDecl mib => Forall oib_scoped mib.(ExAst.ind_bodies)
  | ExAst.TypeAliasDecl _ => False (* never emitted *)
  end.

Lemma emit_decl_scoped T E d : decl_scoped (snd (emit_decl T E d)).
Proof.
  destruct d as [kn [cb|mib]]; cbn.
  - unfold emit_const; cbn. destruct (sch_lookup E kn) as [sch|].
    + apply emit_scheme_closed.
    + intros n [].
  - unfold emit_mib, mapi; cbn. generalize 0 as k.
    induction (EAst.ind_bodies mib) as [|o os IH]; intros k; cbn; constructor; [|apply IH].
    apply emit_oib_scoped.
Qed.

Theorem infer_scoped (Σ : EAst.global_context) (Σ' : ExAst.global_env) :
  infer Σ = Ok Σ' -> Forall (fun '(_, _, d) => decl_scoped d) Σ'.
Proof.
  unfold infer. destruct (init_sigs Σ 0) as [T cnt].
  destruct (infer_go Σ T _) as [[[T1 E1] S1]|e]; cbn; intros H; [|discriminate].
  injection H as <-. apply Forall_map, Forall_forall.
  intros d _. pose proof (emit_decl_scoped T1 E1 d) as Hd.
  destruct (emit_decl T1 E1 d) as [[kn b] d']. exact Hd.
Qed.

(** The Rust/Elm printers resolve [TVar n] by [nth_error] in a context built
    from the scheme's quantifier list ([print_constant]); on inferred schemes
    this lookup never fails. *)
Corollary infer_tvars_resolve (Σ : EAst.global_context) (Σ' : ExAst.global_env) kn b cb {A} (Γ : list A) :
  infer Σ = Ok Σ' ->
  In (kn, b, ExAst.ConstantDecl cb) Σ' ->
  length Γ = length (fst cb.(ExAst.cst_type)) ->
  forall n, In n (ftv (snd cb.(ExAst.cst_type))) -> nth_error Γ n <> None.
Proof.
  intros Hinf Hin HΓ n Hn.
  pose proof (proj1 (Forall_forall _ _) (infer_scoped Σ Σ' Hinf) _ Hin) as Hc.
  apply nth_error_Some. rewrite HΓ. apply Hc, Hn.
Qed.

(** ** Instantiation renames exactly the bound variables into the fresh region *)

Lemma renaming_lookup_some vs base k m u :
  slookup (combine vs (map (fun i => ExAst.TVar (base + i)) (seq k (length vs)))) m = Some u ->
  exists i, k <= i < k + length vs /\ u = ExAst.TVar (base + i).
Proof.
  revert k. induction vs as [|v vs IH]; intros k; cbn; [discriminate|].
  destruct (Nat.eqb_spec m v) as [->|Hne].
  - intros H. injection H as <-. exists k. split; [lia|reflexivity].
  - intros H. apply IH in H as (i & Hi & ->). exists i. split; [lia|reflexivity].
Qed.

Lemma renaming_lookup_none vs base k m :
  slookup (combine vs (map (fun i => ExAst.TVar (base + i)) (seq k (length vs)))) m = None ->
  ~ In m vs.
Proof.
  revert k. induction vs as [|v vs IH]; intros k; cbn; [tauto|].
  destruct (Nat.eqb_spec m v) as [->|Hne]; [discriminate|].
  intros H [Heq|Hin]; [congruence|]. eapply IH; eauto.
Qed.

Lemma instantiate_vars base vs body n :
  In n (ftv (fst (instantiate base (vs, body)))) ->
  (base <= n < base + length vs) \/ (In n (ftv body) /\ ~ In n vs).
Proof.
  unfold instantiate, renaming; cbn.
  induction body as [| |a IHa b IHb|a IHa b IHb|m| |]; cbn; intros Hn; try contradiction.
  - apply in_app_iff in Hn. destruct Hn as [Hn|Hn];
      [destruct (IHa Hn) as [?|[? ?]]|destruct (IHb Hn) as [?|[? ?]]];
      [left|right; split; [apply in_app_iff|]|left|right; split; [apply in_app_iff|]]; auto.
  - apply in_app_iff in Hn. destruct Hn as [Hn|Hn];
      [destruct (IHa Hn) as [?|[? ?]]|destruct (IHb Hn) as [?|[? ?]]];
      [left|right; split; [apply in_app_iff|]|left|right; split; [apply in_app_iff|]]; auto.
  - destruct (slookup _ m) as [u|] eqn:Hl.
    + apply renaming_lookup_some in Hl as (i & Hi & ->). cbn in Hn.
      destruct Hn as [<-|[]]. left. lia.
    + apply renaming_lookup_none in Hl. cbn in Hn. destruct Hn as [<-|[]].
      right. split; [left; reflexivity|exact Hl].
Qed.

(** A scheme whose free variables are all bound instantiates entirely into
    the fresh region. *)
Corollary instantiate_fresh base vs body :
  (forall n, In n (ftv body) -> In n vs) ->
  forall n, In n (ftv (fst (instantiate base (vs, body)))) ->
            base <= n < base + length vs.
Proof.
  intros Hc n Hn. destruct (instantiate_vars base vs body n Hn) as [?|[Hb Hnb]]; [assumption|].
  exfalso. apply Hnb, Hc, Hb.
Qed.

Print Assumptions infer_scoped.
Print Assumptions infer_tvars_resolve.
Print Assumptions instantiate_vars.
Print Assumptions instantiate_fresh.
