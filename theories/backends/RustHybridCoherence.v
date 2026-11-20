(** * A model of the hand-written part of [rust-hybrid]

    The arithmetic of [rust-hybrid] is extracted from [HybridRuntime.v], which
    proves it.  The kernel [mod __hybrid], [__int]/[__num], the comparisons
    and the eliminator macros of [RustHybridRemaps.v] stay hand-written Rust
    strings, which Rocq cannot read.  This file models what they compute, over
    [Z], and proves:

    - the tagged word: [2v+1] encodes a small [v], and the decoded value is
      [v] (an arithmetic shift right by one);
    - [__int] and [__num] build the canonical number of an integer;
    - equality and comparison on canonical numbers, including a small against
      a big one decided by the sign of the big one, are [Z.eqb] and
      [Z.compare];
    - the eliminators: the case and the sub-value they compute from a number
      are the constructor and the argument of the [nat], [positive], [N] or
      [Z] it denotes.

    Trusted: that each Rust string computes the function modelled here, rug
    and GMP. *)

From Stdlib Require Import Bool ZArith NArith PArith Arith Lia.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

(** ** The tagged word *)

Notation P62 := 4611686018427387904%Z (only parsing).
Notation P63 := 9223372036854775808%Z (only parsing).
Lemma P62_pow : P62 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma P63_pow : P63 = 2 ^ 63. Proof. reflexivity. Qed.

(** The small range [__SMIN ..= __SMAX] and the range of [i64]. *)
Definition small (v : Z) : Prop := - P62 <= v <= P62 - 1.
Definition in_i64 (w : Z) : Prop := - P63 <= w <= P63 - 1.

(** Rust's [checked_*] on [i64], given the exact result. *)
Definition checked (w : Z) : option Z :=
  if (- P63 <=? w) && (w <=? P63 - 1) then Some w else None.

Lemma checked_spec w : checked w = if (- P63 <=? w) && (w <=? P63 - 1) then Some w else None.
Proof. reflexivity. Qed.

Definition enc (v : Z) : Z := 2 * v + 1.
Definition dec (w : Z) : Z := Z.shiftr w 1.

Lemma dec_div2 w : dec w = w / 2.
Proof. unfold dec. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Theorem enc_word v : small v -> in_i64 (enc v) /\ Z.odd (enc v) = true /\ dec (enc v) = v.
Proof.
  unfold small, in_i64, enc. intros H. repeat split; try lia.
  - rewrite Z.add_comm, Z.odd_add_mul_2. reflexivity.
  - rewrite dec_div2. symmetry. apply (Z.div_unique _ _ _ 1); lia.
Qed.

(** [checked w = Some w] exactly when [w] is in [i64]. *)
Lemma checked_some w : in_i64 w -> checked w = Some w.
Proof.
  unfold in_i64, checked. intros [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite H1, H2. reflexivity.
Qed.

Lemma checked_none w : ~ in_i64 w -> checked w = None.
Proof.
  unfold in_i64, checked. intros H.
  destruct (- P63 <=? w) eqn:E1, (w <=? P63 - 1) eqn:E2; try reflexivity.
  apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma in_i64_enc s : in_i64 (enc s) <-> small s.
Proof. unfold in_i64, small, enc. lia. Qed.

Lemma in_i64_double s : in_i64 (2 * s) <-> small s.
Proof. unfold in_i64, small. lia. Qed.

(** ** Canonical numbers *)

(** [View::S v] or [View::B z]. *)
Inductive num := S (v : Z) | B (z : Z).

Definition den (n : num) : Z := match n with S v => v | B z => z end.
Definition canonical (n : num) : Prop := match n with S v => small v | B z => ~ small z end.

(** [__int] and [__num]: the canonical number of an integer. *)
Definition mk (z : Z) : num := if (- P62 <=? z) && (z <=? P62 - 1) then S z else B z.

Theorem mk_spec z : canonical (mk z) /\ den (mk z) = z.
Proof.
  unfold mk, canonical, small.
  destruct (- P62 <=? z) eqn:E1, (z <=? P62 - 1) eqn:E2; simpl;
    try apply Z.leb_le in E1; try apply Z.leb_le in E2;
    try apply Z.leb_gt in E1; try apply Z.leb_gt in E2; split; auto; lia.
Qed.

(** [PartialEq]: a small and a big number are never equal. *)
Definition num_eqb (a b : num) : bool :=
  match a, b with S x, S y => Z.eqb x y | B x, B y => Z.eqb x y | _, _ => false end.

Theorem num_eqb_spec a b : canonical a -> canonical b -> num_eqb a b = Z.eqb (den a) (den b).
Proof.
  destruct a as [x|x], b as [y|y]; simpl; intros Ha Hb; try reflexivity;
    symmetry; apply Z.eqb_neq; intros ->; contradiction.
Qed.

(** [Ord]: a small against a big number is decided by the big one's sign
    ([cmp0], reversed when the big one is on the right). *)
Definition num_cmp (a b : num) : comparison :=
  match a, b with
  | S x, S y => Z.compare x y
  | S _, B z => CompOpp (Z.compare z 0)
  | B z, S _ => Z.compare z 0
  | B x, B y => Z.compare x y
  end.

Theorem num_cmp_spec a b : canonical a -> canonical b -> num_cmp a b = Z.compare (den a) (den b).
Proof.
  destruct a as [x|x], b as [y|y]; simpl; intros Ha Hb; try reflexivity; unfold small in *.
  - destruct (Z.compare_spec y 0); simpl; symmetry;
      [ exfalso; apply Hb; lia | apply Z.compare_gt_iff; lia | apply Z.compare_lt_iff; lia ].
  - destruct (Z.compare_spec x 0); simpl; symmetry;
      [ exfalso; apply Ha; lia | apply Z.compare_lt_iff; lia | apply Z.compare_gt_iff; lia ].
Qed.

(** ** Eliminators *)

(** [__nat_elim]: zero, or the predecessor. *)
Theorem nat_elim_spec n : (Z.of_nat n = 0 <-> n = O) /\
  (forall m, n = Datatypes.S m -> Z.of_nat n - 1 = Z.of_nat m).
Proof. split; [lia|]. intros m ->. lia. Qed.

(** [__pos_elim]: [1] is [xH]; otherwise the parity selects [xI]/[xO], and the
    argument is the number shifted right by one ([n >> 1], [b >> 1u32]). *)
Definition pos_case (v : Z) : nat * Z :=
  if Z.eqb v 1 then (2%nat, 0) else if Z.odd v then (0%nat, Z.shiftr v 1) else (1%nat, Z.shiftr v 1).

Theorem pos_elim_spec p :
  pos_case (Z.pos p) =
    match p with xI q => (0%nat, Z.pos q) | xO q => (1%nat, Z.pos q) | xH => (2%nat, 0) end.
Proof.
  unfold pos_case. destruct p as [q|q|]; [| |reflexivity].
  - rewrite Pos2Z.inj_xI. replace (Z.eqb (2 * Z.pos q + 1) 1) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.add_comm, Z.odd_add_mul_2. simpl Z.odd. rewrite Z.shiftr_div_pow2 by lia.
    f_equal. symmetry. apply (Z.div_unique _ _ _ 1); lia.
  - rewrite Pos2Z.inj_xO. replace (Z.eqb (2 * Z.pos q) 1) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.odd_mul, Z.odd_2. simpl. rewrite Z.shiftr_div_pow2 by lia.
    f_equal. symmetry. apply (Z.div_unique _ _ _ 0); lia.
Qed.

(** [__N_elim]: zero, or the positive number itself. *)
Theorem N_elim_spec n : (Z.of_N n = 0 <-> n = N0) /\ (forall p, n = Npos p -> Z.of_N n = Z.pos p).
Proof. split; [lia|]. intros p ->. reflexivity. Qed.

(** [__Z_elim]: zero, the positive number itself, or the negation of a negative one. *)
Theorem Z_elim_spec z :
  match z with Z0 => z = 0 | Zpos p => 0 < z /\ z = Z.pos p | Zneg p => z < 0 /\ - z = Z.pos p end.
Proof. destruct z; lia. Qed.
