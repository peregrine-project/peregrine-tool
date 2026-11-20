(** * De Bruijn lemmas for the lambda-box rewrites

    Facts about [exchange], [mk_lambdas], [strip_lambdas] and closed
    substitution, used by the simulation proof of [ELboxOptsSim]. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv.
From Peregrine Require Import ELboxOpts.

Local Open Scope bool_scope.
Set Default Goal Selector "!".

Ltac nat_cases :=
  repeat (cbn -[Nat.ltb Nat.compare];
          match goal with
          | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec x y)
          | |- context [Nat.compare ?x ?y] => destruct (Nat.compare_spec x y)
          end);
  cbn -[Nat.ltb Nat.compare]; try lia; try (f_equal; lia).

Ltac ih_tac :=
  match goal with IH : forall _ _, _ -> _ = _ |- _ => apply IH; lia end.

Ltac fix_tac :=
  f_equal; rewrite !map_map;
  match goal with X : All _ ?m |- map _ ?m = map _ ?m =>
    eapply All_map_eq; eapply All_impl; [exact X|];
    cbn; intros ? IH; unfold map_def; cbn; f_equal; apply IH; lia end.

(** ** [exchange] *)

Lemma closedn_exchange m n k j t :
  k + m + n <= j -> closedn j t -> closedn j (exchange m n k t).
Proof.
  induction t in k, j |- * using term_forall_list_ind; intros hle cl;
    cbn -[Nat.ltb] in *; rtoProp; intuition auto.
  all: try solve [solve_all].
  all: try solve [match goal with IH : forall k j, _ |- _ => eapply IH; [|eassumption]; lia end].
  all: rewrite ?length_map.
  all: try solve [solve_all;
    match goal with a : forall k j, _ |- _ => eapply a; [|eassumption]; lia end].
  - apply Nat.ltb_lt in cl. nat_cases; try reflexivity.
  - rewrite test_prim_map.
    eapply primProp_impl_test_prim.
    match goal with H : is_true (test_prim _ _) |- _ => eapply test_prim_impl_primProp in H;
      eapply primProp_impl; [exact (primProp_conj X H)|] end.
    cbn. intros x [h1 h2]. eapply h1; [exact hle|exact h2].
Qed.

Lemma exchange_closed m n d t : closedn d t -> exchange m n d t = t.
Proof.
  induction t in d |- * using term_forall_list_ind; intros cl;
    cbn -[Nat.ltb] in *; rtoProp; try solve [f_equal; intuition auto; solve_all].
  apply Nat.ltb_lt in cl. nat_cases.
Qed.

Lemma exchange_0 m d t : exchange m 0 d t = t.
Proof.
  induction t in d |- * using term_forall_list_ind;
    cbn -[Nat.ltb] in *; try solve [f_equal; intuition auto; solve_all].
  nat_cases.
Qed.

(** Substitution beyond the exchanged blocks. *)
Lemma csubst_exchange a m n d k t :
  closed a -> d + m + n <= k ->
  csubst a k (exchange m n d t) = exchange m n d (csubst a k t).
Proof.
  intros ca. induction t in d, k |- * using term_forall_list_ind; intros hle;
    cbn -[Nat.ltb Nat.compare] in *; rewrite ?length_map;
    try solve [f_equal; intuition auto; solve_all; try (ih_tac)].
  all: try solve [fix_tac].
  nat_cases.
  rewrite exchange_closed //. eapply closed_upwards; tea. lia.
Qed.

(** Substitution for the first variable of the outer block. *)
Lemma csubst_exchange_near a m n d e t :
  closed a -> e = m + d ->
  csubst a d (exchange m (S n) d t) = exchange m n d (csubst a e t).
Proof.
  intros ca. induction t in d, e |- * using term_forall_list_ind; intros he;
    cbn -[Nat.ltb Nat.compare] in *;
    rewrite ?length_map;
    try solve [f_equal; intuition auto; solve_all; try (ih_tac)].
  all: try solve [fix_tac].
  subst e. nat_cases.
  all: try (rewrite exchange_closed //; eapply closed_upwards; tea; lia).
Qed.

Definition substl_at k s t := fold_left (fun b a => csubst a k b) s t.

Lemma substl_at_exchange m d s t :
  forallb (closedn 0) s ->
  substl_at d s (exchange m #|s| d t) = substl_at (m + d) s t.
Proof.
  induction s in t |- *; cbn; [now rewrite exchange_0|].
  move/andP => [ca cs]. rewrite (csubst_exchange_near a m #|s| d (m + d)) //.
  now apply IHs.
Qed.

Lemma substl_at_0 s t : substl_at 0 s t = substl s t.
Proof. reflexivity. Qed.

(** ** Commuting closed substitutions *)

Lemma csubst_csubst a w j b :
  closed a -> closed w ->
  csubst a j (csubst w 0 b) = csubst w 0 (csubst a (S j) b).
Proof.
  intros ca cw. rewrite !closed_subst //.
  rewrite (distr_subst [a] [w] b j). cbn.
  rewrite (subst_closed _ _ w) //. eapply closed_upwards; tea. lia.
Qed.

Lemma csubst_substl a j s x :
  closed a -> forallb (closedn 0) s ->
  csubst a j (substl s x) = substl s (csubst a (#|s| + j) x).
Proof.
  intros ca. unfold substl. induction s in x |- *; cbn; auto.
  move/andP => [cw cs]. rewrite IHs // csubst_csubst //.
Qed.

(** ** [mk_lambdas], [strip_lambdas], [has_lambdas] *)

Lemma csubst_mk_lambdas a k xs e :
  csubst a k (mk_lambdas xs e) = mk_lambdas xs (csubst a (#|xs| + k) e).
Proof.
  induction xs in k |- *; cbn; auto. rewrite IHxs. do 3 f_equal. lia.
Qed.

Lemma substl_mk_lambdas s xs e :
  substl s (mk_lambdas xs e) = mk_lambdas xs (substl_at #|xs| s e).
Proof.
  unfold substl, substl_at. induction s in e |- *; cbn; auto.
  now rewrite csubst_mk_lambdas Nat.add_0_r.
Qed.

Lemma closedn_mk_lambdas k xs e :
  closedn k (mk_lambdas xs e) = closedn (#|xs| + k) e.
Proof.
  induction xs in k |- *; cbn; auto. rewrite IHxs. f_equal. lia.
Qed.

Lemma mk_lambdas_strip m t :
  has_lambdas m t -> t = mk_lambdas (lambda_names m t) (strip_lambdas m t).
Proof.
  induction m in t |- *; destruct t; cbn; try discriminate; auto.
  intros H. f_equal. now apply IHm.
Qed.

Lemma length_lambda_names_has m t : has_lambdas m t -> #|lambda_names m t| = m.
Proof.
  induction m in t |- *; destruct t; cbn; try discriminate; auto.
  intros H. f_equal. now apply IHm.
Qed.

Lemma count_has_lambdas m t : m <= count_lambdas t -> has_lambdas m t.
Proof.
  induction m in t |- *; destruct t; cbn; auto; try lia.
  intros H. apply IHm. lia.
Qed.

Lemma has_lambdas_csubst a k m t : has_lambdas m t -> has_lambdas m (csubst a k t).
Proof.
  induction m in k, t |- *; destruct t; cbn; try discriminate; auto.
Qed.

Lemma strip_lambdas_csubst a k m t :
  has_lambdas m t ->
  strip_lambdas m (csubst a k t) = csubst a (m + k) (strip_lambdas m t).
Proof.
  induction m in k, t |- *; destruct t; cbn; try discriminate; auto.
  intros H. rewrite IHm //. do 2 f_equal. lia.
Qed.

Lemma closedn_strip_lambdas m k t :
  has_lambdas m t -> closedn k t -> closedn (m + k) (strip_lambdas m t).
Proof.
  induction m in k, t |- *; destruct t; cbn; try discriminate; auto.
  intros H cl. replace (S (m + k)) with (m + S k) by lia. now apply IHm.
Qed.
