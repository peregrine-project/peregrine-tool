(** * A model of the [rust-hybrid] numbers, and the remaps checked against it

    [RustHybridRemaps.v] prints Rust source strings, which Rocq cannot read.
    This file models what those strings compute, over [Z], and proves:

    - the tagged word: [2v+1] encodes a small [v], and the decoded value is
      [v] (an arithmetic shift right by one);
    - the fast paths: on two small arguments, [checked_add (2x+1) (2y)],
      [checked_sub (2x+1) (2y)] and [checked_mul (2x) y] succeed exactly when the
      result is small, and then give its encoding, so every result is canonical;
    - floor division and its remainder computed from Rust's truncating [/]
      and [%] are [Z.div] and [Z.modulo], and the remainder of two small
      numbers is small;
    - equality and comparison on canonical numbers, including a small against
      a big one decided by the sign of the big one, are [Z.eqb] and
      [Z.compare];
    - the eliminators: the case and the sub-value they compute from a number
      are the constructor and the argument of the [nat], [positive], [N] or
      [Z] it denotes;
    - every entry of the remap table: the modelled operation, applied to the
      integers that the arguments denote, gives the integer that the Rocq
      function's result denotes (e.g. [Nat.sub] clamps at 0, [Pos.pred] and
      [Pos.sub] at 1, division by 0 gives 0, the remainder of a division by
      0 is the dividend).

    Trusted, as in [RustMixedCoherence.v]: that each emitted Rust string
    computes the function modelled here (Rust's [checked_*], [/], [%], [>>]
    on [i64]; rug's operations as the corresponding [Z] functions), and GMP.
    [__pow] aborts on an exponent outside [u32] unless the base is 0 or 1; the
    model covers the others. *)

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

(** The fast path of a binary operation: [Some] of the encoded result when it
    is small, [None] (go to GMP) otherwise. *)
Definition fast (s : Z) : option Z := if (- P62 <=? s) && (s <=? P62 - 1) then Some (enc s) else None.

Lemma fast_spec s : (small s -> fast s = Some (enc s)) /\ (~ small s -> fast s = None).
Proof.
  unfold fast, small. split; intros H.
  - destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite H1, H2. reflexivity.
  - destruct (- P62 <=? s) eqn:E1, (s <=? P62 - 1) eqn:E2; try reflexivity.
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma checked_enc s : checked (enc s) = fast s.
Proof.
  destruct (fast_spec s) as [Hs Hn].
  destruct (Z.le_gt_cases (- P62) s), (Z.le_gt_cases s (P62 - 1)).
  - rewrite Hs by (unfold small; lia). apply checked_some, in_i64_enc. unfold small; lia.
  - rewrite Hn by (unfold small; lia). apply checked_none. rewrite in_i64_enc. unfold small; lia.
  - rewrite Hn by (unfold small; lia). apply checked_none. rewrite in_i64_enc. unfold small; lia.
  - lia.
Qed.

(** [add_small]: [a.0.checked_add(b.0 - 1)]; [b.0 - 1] does not overflow. *)
Theorem add_small_spec x y : small x -> small y ->
  in_i64 (enc y - 1) /\ checked (enc x + (enc y - 1)) = fast (x + y).
Proof.
  intros Hx Hy. split.
  - unfold in_i64, enc, small in *. lia.
  - replace (enc x + (enc y - 1)) with (enc (x + y)) by (unfold enc; lia).
    apply checked_enc.
Qed.

(** [sub_small]: [a.0.checked_sub(b.0 - 1)]. *)
Theorem sub_small_spec x y : small x -> small y ->
  checked (enc x - (enc y - 1)) = fast (x - y).
Proof.
  intros Hx Hy. replace (enc x - (enc y - 1)) with (enc (x - y)) by (unfold enc; lia).
  apply checked_enc.
Qed.

(** [mul_small]: [(a.0 - 1).checked_mul(b.0 >> 1)], then [r + 1]; [r] is even,
    so [r + 1] does not overflow. *)
Theorem mul_small_spec x y : small x -> small y ->
  dec (enc y) = y /\
  option_map (fun r => r + 1) (checked ((enc x - 1) * dec (enc y))) = fast (x * y).
Proof.
  intros Hx Hy. destruct (enc_word y Hy) as [_ [_ Hd]]. split; [exact Hd|]. rewrite Hd.
  replace ((enc x - 1) * y) with (2 * (x * y)) by (unfold enc; lia).
  destruct (fast_spec (x * y)) as [Hs Hn].
  destruct (Z.le_gt_cases (- P62) (x * y)), (Z.le_gt_cases (x * y) (P62 - 1)).
  - rewrite Hs by (unfold small; lia). rewrite checked_some by (apply in_i64_double; unfold small; lia).
    simpl. unfold enc. f_equal; lia.
  - rewrite Hn by (unfold small; lia). rewrite checked_none by (rewrite in_i64_double; unfold small; lia). reflexivity.
  - rewrite Hn by (unfold small; lia). rewrite checked_none by (rewrite in_i64_double; unfold small; lia). reflexivity.
  - lia.
Qed.

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

(** ** Floor division and remainder from Rust's truncating [/] and [%] *)

Definition divf_small (x y : Z) : Z :=
  let q := Z.quot x y in let r := Z.rem x y in
  if negb (Z.eqb r 0) && xorb (Z.ltb r 0) (Z.ltb y 0) then q - 1 else q.

Definition modf_small (x y : Z) : Z :=
  let r := Z.rem x y in
  if negb (Z.eqb r 0) && xorb (Z.ltb r 0) (Z.ltb y 0) then r + y else r.

Lemma quot_rem_facts x y : y <> 0 ->
  x = y * Z.quot x y + Z.rem x y /\ Z.abs (Z.rem x y) < Z.abs y /\
  (0 <= x -> 0 <= Z.rem x y) /\ (x <= 0 -> Z.rem x y <= 0).
Proof.
  intros Hy. split; [apply Z.quot_rem; exact Hy|]. split; [apply Z.rem_bound_abs; exact Hy|].
  split; intros H.
  - apply Z.rem_nonneg; lia.
  - apply Z.rem_nonpos; lia.
Qed.

Theorem divf_small_spec x y : y <> 0 -> divf_small x y = Z.div x y /\ modf_small x y = Z.modulo x y.
Proof.
  intros Hy. destruct (quot_rem_facts x y Hy) as [Hqr [Hb [Hp Hn]]].
  unfold divf_small, modf_small. cbv zeta.
  set (q := Z.quot x y) in *. set (r := Z.rem x y) in *.
  destruct (Z.eqb_spec r 0) as [Hr0|Hr0]; destruct (Z.ltb_spec r 0); destruct (Z.ltb_spec y 0); simpl.
  all: first
    [ split; [apply (Z.div_unique _ _ _ r) | apply (Z.mod_unique _ _ q)]; lia
    | split; [apply (Z.div_unique _ _ _ (r + y)) | apply (Z.mod_unique _ _ (q - 1))]; lia ].
Qed.

(** [__divf] and [__modf] by 0: [x / 0 = 0] and [x mod 0 = x], as in Rocq. *)
Lemma div_0 x : Z.div x 0 = 0. Proof. destruct x; reflexivity. Qed.
Lemma mod_0 x : Z.modulo x 0 = x. Proof. destruct x; reflexivity. Qed.

(** The remainder of two small numbers is small, so [__modf] builds it with
    [Num::S] without a range check. *)
Theorem modf_small_small x y : small y -> y <> 0 -> small (Z.modulo x y).
Proof.
  unfold small. intros Hy H0.
  destruct (Z.ltb_spec 0 y).
  - pose proof (Z.mod_pos_bound x y ltac:(lia)). lia.
  - pose proof (Z.mod_neg_bound x y ltac:(lia)). lia.
Qed.

(** The [clamp] of a remap: [if r < lo { lo } else { r }]. *)
Definition clamp (lo r : Z) : Z := if Z.ltb r lo then lo else r.
Lemma clamp_max lo r : clamp lo r = Z.max lo r.
Proof. unfold clamp. destruct (Z.ltb_spec r lo); lia. Qed.

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

(** ** The remap table

    Each entry, on the integers that the arguments denote, gives the integer
    that the Rocq function's result denotes.  The constructors: [S] is [+ 1],
    [xI]/[xO]/[xH] are [2x + 1], [2x] and [1], [N0]/[Npos] are [0] and the
    identity, [Z0]/[Zpos]/[Zneg] are [0], the identity and the negation. *)

Section nat_remaps.
  Variables a b : nat.
  Lemma r_nat_succ : Z.of_nat (Datatypes.S a) = Z.of_nat a + 1. Proof. lia. Qed.
  Lemma r_nat_add : Z.of_nat (a + b) = Z.of_nat a + Z.of_nat b. Proof. lia. Qed.
  Lemma r_nat_mul : Z.of_nat (a * b) = Z.of_nat a * Z.of_nat b. Proof. lia. Qed.
  Lemma r_nat_sub : Z.of_nat (a - b) = clamp 0 (Z.of_nat a - Z.of_nat b).
  Proof. rewrite clamp_max. lia. Qed.
  Lemma r_nat_eqb : Nat.eqb a b = Z.eqb (Z.of_nat a) (Z.of_nat b).
  Proof. destruct (Nat.eqb_spec a b), (Z.eqb_spec (Z.of_nat a) (Z.of_nat b)); lia. Qed.
  Lemma r_nat_leb : Nat.leb a b = Z.leb (Z.of_nat a) (Z.of_nat b).
  Proof. destruct (Nat.leb_spec a b), (Z.leb_spec (Z.of_nat a) (Z.of_nat b)); lia. Qed.
  Lemma r_nat_ltb : Nat.ltb a b = Z.ltb (Z.of_nat a) (Z.of_nat b).
  Proof. destruct (Nat.ltb_spec a b), (Z.ltb_spec (Z.of_nat a) (Z.of_nat b)); lia. Qed.
  Lemma r_nat_compare : Nat.compare a b = Z.compare (Z.of_nat a) (Z.of_nat b).
  Proof. symmetry. apply Nat2Z.inj_compare. Qed.
  Lemma r_nat_max : Z.of_nat (Nat.max a b) = Z.max (Z.of_nat a) (Z.of_nat b). Proof. lia. Qed.
  Lemma r_nat_min : Z.of_nat (Nat.min a b) = Z.min (Z.of_nat a) (Z.of_nat b). Proof. lia. Qed.
  Lemma r_nat_div : Z.of_nat (Nat.div a b) = Z.div (Z.of_nat a) (Z.of_nat b).
  Proof. apply Nat2Z.inj_div. Qed.
  Lemma r_nat_mod : Z.of_nat (Nat.modulo a b) = Z.modulo (Z.of_nat a) (Z.of_nat b).
  Proof. apply Nat2Z.inj_mod. Qed.
  Lemma r_nat_pow : Z.of_nat (Nat.pow a b) = Z.pow (Z.of_nat a) (Z.of_nat b).
  Proof. apply Nat2Z.inj_pow. Qed.
End nat_remaps.

Section pos_remaps.
  Variables a b : positive.
  Lemma r_pos_xI : Z.pos (xI a) = 2 * Z.pos a + 1. Proof. reflexivity. Qed.
  Lemma r_pos_xO : Z.pos (xO a) = 2 * Z.pos a. Proof. reflexivity. Qed.
  Lemma r_pos_add : Z.pos (a + b) = Z.pos a + Z.pos b. Proof. reflexivity. Qed.
  Lemma r_pos_succ : Z.pos (Pos.succ a) = Z.pos a + 1. Proof. apply Pos2Z.inj_succ. Qed.
  Lemma r_pos_pred : Z.pos (Pos.pred a) = clamp 1 (Z.pos a - 1).
  Proof.
    rewrite clamp_max. destruct (Pos.eq_dec a 1) as [->|H]; [reflexivity|].
    rewrite Pos2Z.inj_pred by exact H. lia.
  Qed.
  Lemma r_pos_sub : Z.pos (Pos.sub a b) = clamp 1 (Z.pos a - Z.pos b).
  Proof. rewrite clamp_max. apply Pos2Z.inj_sub_max. Qed.
  Lemma r_pos_mul : Z.pos (a * b) = Z.pos a * Z.pos b. Proof. reflexivity. Qed.
  Lemma r_pos_min : Z.pos (Pos.min a b) = Z.min (Z.pos a) (Z.pos b). Proof. apply Pos2Z.inj_min. Qed.
  Lemma r_pos_max : Z.pos (Pos.max a b) = Z.max (Z.pos a) (Z.pos b). Proof. apply Pos2Z.inj_max. Qed.
  Lemma r_pos_eqb : Pos.eqb a b = Z.eqb (Z.pos a) (Z.pos b). Proof. reflexivity. Qed.
  Lemma r_pos_compare : Pos.compare a b = Z.compare (Z.pos a) (Z.pos b). Proof. reflexivity. Qed.
End pos_remaps.

Section N_remaps.
  Variables a b : N.
  Lemma r_N_add : Z.of_N (a + b) = Z.of_N a + Z.of_N b. Proof. lia. Qed.
  Lemma r_N_succ : Z.of_N (N.succ a) = Z.of_N a + 1. Proof. lia. Qed.
  Lemma r_N_pred : Z.of_N (N.pred a) = clamp 0 (Z.of_N a - 1).
  Proof. rewrite clamp_max. apply N2Z.inj_pred_max. Qed.
  Lemma r_N_sub : Z.of_N (a - b) = clamp 0 (Z.of_N a - Z.of_N b).
  Proof. rewrite clamp_max. apply N2Z.inj_sub_max. Qed.
  Lemma r_N_mul : Z.of_N (a * b) = Z.of_N a * Z.of_N b. Proof. lia. Qed.
  Lemma r_N_div : Z.of_N (N.div a b) = Z.div (Z.of_N a) (Z.of_N b). Proof. apply N2Z.inj_div. Qed.
  Lemma r_N_mod : Z.of_N (N.modulo a b) = Z.modulo (Z.of_N a) (Z.of_N b). Proof. apply N2Z.inj_mod. Qed.
  Lemma r_N_min : Z.of_N (N.min a b) = Z.min (Z.of_N a) (Z.of_N b). Proof. lia. Qed.
  Lemma r_N_max : Z.of_N (N.max a b) = Z.max (Z.of_N a) (Z.of_N b). Proof. lia. Qed.
  Lemma r_N_eqb : N.eqb a b = Z.eqb (Z.of_N a) (Z.of_N b).
  Proof. destruct (N.eqb_spec a b), (Z.eqb_spec (Z.of_N a) (Z.of_N b)); lia. Qed.
  Lemma r_N_compare : N.compare a b = Z.compare (Z.of_N a) (Z.of_N b).
  Proof. symmetry. apply N2Z.inj_compare. Qed.
End N_remaps.

(** [Z] is the model itself, so its arithmetic entries are the identity on the
    model; the entries that change representation are these. *)
Section Z_remaps.
  Variables (z : Z) (n : N).
  Lemma r_Z_of_N : Z.of_N n = Z.of_N n. Proof. reflexivity. Qed.
  Lemma r_Z_abs_N : Z.of_N (Z.abs_N z) = Z.abs z. Proof. apply N2Z.inj_abs_N. Qed.
  Lemma r_Z_neg p : Z.neg p = - Z.pos p. Proof. reflexivity. Qed.
End Z_remaps.
