(** * The [rust-hybrid] number runtime, written in Rocq

    The arithmetic of [rust-hybrid] over the primitives of [HybridPrims.v]:
    a fast path on small numbers and a GMP slow path for each operation,
    floor division, power, the comparisons, and the functions that the remap
    table of [HybridRuntimeRemaps.v] sends [nat], [positive], [N] and [Z]
    operations to.  Peregrine's own Rust backend prints these definitions
    into the program preamble, so the Rust that runs is extracted from them.

    Proved, assuming the primitive models:
    - each operation computes the integer operation ([add_spec], ...,
      [pow_spec]);
    - the fast paths keep the representation canonical and call the unchecked
      primitives only within their preconditions ([add_fast_ok], ...);
    - each function of the remap table agrees with the Rocq function it
      replaces, through the embedding of [nat], [positive], [N] and [Z]
      ([nat_add_ok], ..., [Z_abs_N_ok]). *)

From Stdlib Require Import Bool ZArith Arith NArith PArith Lia.
From Peregrine Require Import HybridPrims.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** The runtime *)

Definition zero : num := num_S i_0.
Definition one : num := num_S i_1.
Definition two : num := num_S i_2.

(** Addition and subtraction add [2y] to the word [2x+1]; multiplication
    multiplies [2x] by [y].  [checked_*] overflows exactly when the result
    leaves the small range. *)
Definition add (a b : num) : num :=
  if num_both_small a b then
    match i_checked_add (num_word a) (i_sub (num_word b) i_1) with
    | ISome r => num_of_word r
    | INone => big_add a b
    end
  else big_add a b.

Definition sub (a b : num) : num :=
  if num_both_small a b then
    match i_checked_sub (num_word a) (i_sub (num_word b) i_1) with
    | ISome r => num_of_word r
    | INone => big_sub a b
    end
  else big_sub a b.

Definition mul (a b : num) : num :=
  if num_both_small a b then
    match i_checked_mul (i_sub (num_word a) i_1) (i_shr1 (num_word b)) with
    | ISome r => num_of_word (i_add r i_1)
    | INone => big_mul a b
    end
  else big_mul a b.

Definition neg (a : num) : num :=
  match num_small a with
  | ISome x => num_int (i_neg x)
  | INone => big_neg a
  end.

Definition abs (a : num) : num :=
  match num_small a with
  | ISome x => num_int (i_abs x)
  | INone => big_abs a
  end.

(** Floor division from the truncating one: correct the quotient (and the
    remainder) when the remainder is non-zero and of the other sign than
    the divisor. *)
Definition floor_fix (r y : i64) : bool :=
  if i_eqb r i_0 then false
  else if i_ltb r i_0 then (if i_ltb y i_0 then false else true)
  else i_ltb y i_0.

(** [x / 0 = 0] and [x mod 0 = x], as in Rocq. *)
Definition divf (a b : num) : num :=
  if num_eqb b zero then zero else
  match num_small a, num_small b with
  | ISome x, ISome y =>
    let q := i_quot x y in
    let r := i_rem x y in
    num_int (if floor_fix r y then i_sub q i_1 else q)
  | _, _ => big_divf a b
  end.

Definition modf (a b : num) : num :=
  if num_eqb b zero then a else
  match num_small a, num_small b with
  | ISome x, ISome y =>
    let r := i_rem x y in
    num_S (if floor_fix r y then i_add r y else r)
  | _, _ => big_modf a b
  end.

(** [b] is a natural number; an exponent outside [u32] is accepted only for
    the bases [0] and [1]. *)
Definition pow (a b : num) : num :=
  match num_small b with
  | ISome e =>
    if i_ltb e i_0 then pow_out_of_range a else
    if i_ltb i_u32max e then pow_out_of_range a else
    match num_small a with
    | ISome x =>
      match i_checked_pow x e with
      | ISome r => num_int r
      | INone => big_pow a e
      end
    | INone => big_pow a e
    end
  | INone => pow_out_of_range a
  end.

Definition leb (a b : num) : bool := match num_compare a b with Gt => false | _ => true end.
Definition ltb (a b : num) : bool := match num_compare a b with Lt => true | _ => false end.
Definition min (a b : num) : num := if leb a b then a else b.
Definition max (a b : num) : num := if leb b a then a else b.
(** [max lo r]. *)
Definition clamp (lo r : num) : num := if ltb r lo then lo else r.

Definition succ (a : num) : num := add a one.
Definition pred (a : num) : num := sub a one.
(** [Nat.sub] and [N.sub] clamp at 0, [Pos.sub] at 1; [N.pred] and
    [Pos.pred] likewise. *)
Definition sub0 (a b : num) : num := clamp zero (sub a b).
Definition sub1 (a b : num) : num := clamp one (sub a b).
Definition pred0 (a : num) : num := clamp zero (sub a one).
Definition pred1 (a : num) : num := clamp one (sub a one).
Definition double_plus_one (a : num) : num := add (mul a two) one.
Definition double (a : num) : num := mul a two.
Definition id (a : num) : num := a.

(** ** Lemmas on the models *)

Lemma smallb_spec v : smallb v = true <-> small v.
Proof. unfold smallb, small. rewrite andb_true_iff, !Z.leb_le. tauto. Qed.

Lemma smallb_false v : smallb v = false -> ~ small v.
Proof. intros H Hs. apply smallb_spec in Hs. congruence. Qed.

Lemma in_i64b_spec w : in_i64b w = true <-> in_i64 w.
Proof. unfold in_i64b, in_i64. rewrite andb_true_iff, !Z.leb_le. tauto. Qed.

Lemma shiftr_enc v : Z.shiftr (2 * v + 1) 1 = v.
Proof.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.mul_comm, Z.div_add_l by lia. change (1 / 2) with 0. lia.
Qed.

Lemma shiftr_double v : Z.shiftr (2 * v) 1 = v.
Proof.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma num_small_spec n :
  num_small n = if smallb (unN n) then ISome (I (unN n)) else INone.
Proof. reflexivity. Qed.

Ltac unfold_prims :=
  unfold num_both_small, num_word, num_of_word, num_S, num_int, num_small,
    i_checked_add, i_checked_sub, i_checked_mul, i_checked_pow, checked,
    i_add, i_sub, i_neg, i_abs, i_shr1, i_quot, i_rem, i_eqb, i_ltb,
    i_0, i_1, i_2, i_u32max, big_add, big_sub, big_mul, big_neg, big_abs,
    big_divf, big_modf, big_pow, pow_out_of_range, num_eqb, num_compare in *;
  cbn [unI unN] in *.

(** ** Correctness of the operations *)

Theorem add_spec a b : add a b = Nm (unN a + unN b).
Proof.
  destruct a as [x], b as [y]. unfold add. unfold_prims.
  destruct (smallb x && smallb y); [|reflexivity].
  replace (2 * x + 1 + (2 * y + 1 - 1)) with (2 * (x + y) + 1) by lia.
  destruct (in_i64b (2 * (x + y) + 1)); cbv beta iota; cbn [unI unN]; [|reflexivity].
  now rewrite shiftr_enc.
Qed.

Theorem sub_spec a b : sub a b = Nm (unN a - unN b).
Proof.
  destruct a as [x], b as [y]. unfold sub. unfold_prims.
  destruct (smallb x && smallb y); [|reflexivity].
  replace (2 * x + 1 - (2 * y + 1 - 1)) with (2 * (x - y) + 1) by lia.
  destruct (in_i64b (2 * (x - y) + 1)); cbv beta iota; cbn [unI unN]; [|reflexivity].
  now rewrite shiftr_enc.
Qed.

Theorem mul_spec a b : mul a b = Nm (unN a * unN b).
Proof.
  destruct a as [x], b as [y]. unfold mul. unfold_prims.
  destruct (smallb x && smallb y); [|reflexivity].
  rewrite shiftr_enc.
  replace ((2 * x + 1 - 1) * y) with (2 * (x * y)) by lia.
  destruct (in_i64b (2 * (x * y))); cbv beta iota; cbn [unI unN]; [|reflexivity].
  now rewrite shiftr_enc.
Qed.

Theorem neg_spec a : neg a = Nm (- unN a).
Proof. destruct a as [x]. unfold neg. unfold_prims. now destruct (smallb x). Qed.

Theorem abs_spec a : abs a = Nm (Z.abs (unN a)).
Proof. destruct a as [x]. unfold abs. unfold_prims. now destruct (smallb x). Qed.

Lemma floor_fix_spec r y : floor_fix (I r) (I y) =
  negb (Z.eqb r 0) && xorb (Z.ltb r 0) (Z.ltb y 0).
Proof. unfold floor_fix, i_eqb, i_ltb, i_0. cbn [unI]. now destruct (r =? 0), (r <? 0), (y <? 0). Qed.

Lemma quot_rem_floor x y : y <> 0 ->
  (if negb (Z.eqb (Z.rem x y) 0) && xorb (Z.ltb (Z.rem x y) 0) (Z.ltb y 0)
   then Z.quot x y - 1 else Z.quot x y) = Z.div x y /\
  (if negb (Z.eqb (Z.rem x y) 0) && xorb (Z.ltb (Z.rem x y) 0) (Z.ltb y 0)
   then Z.rem x y + y else Z.rem x y) = Z.modulo x y.
Proof.
  intros Hy.
  pose proof (Z.quot_rem x y Hy) as Hqr.
  pose proof (Z.rem_bound_abs x y Hy) as Hb.
  assert (Hp : 0 <= x -> 0 <= Z.rem x y) by (intros; apply Z.rem_nonneg; lia).
  assert (Hn : x <= 0 -> Z.rem x y <= 0) by (intros; apply Z.rem_nonpos; lia).
  set (q := Z.quot x y) in *. set (r := Z.rem x y) in *.
  destruct (Z.eqb_spec r 0); destruct (Z.ltb_spec r 0); destruct (Z.ltb_spec y 0); simpl.
  all: first
    [ split; [apply (Z.div_unique _ _ _ r) | apply (Z.mod_unique _ _ q)]; lia
    | split; [apply (Z.div_unique _ _ _ (r + y)) | apply (Z.mod_unique _ _ (q - 1))]; lia ].
Qed.

Theorem divf_spec a b : divf a b = Nm (Z.div (unN a) (unN b)).
Proof.
  destruct a as [x], b as [y]. unfold divf, zero. unfold_prims.
  destruct (Z.eqb_spec y 0) as [->|Hy]; [now rewrite Zdiv_0_r|].
  destruct (smallb x), (smallb y); cbv beta iota; cbn [unI unN]; try reflexivity.
  rewrite floor_fix_spec. f_equal.
  destruct (quot_rem_floor x y Hy) as [Hd _].
  destruct (negb (Z.rem x y =? 0) && xorb (Z.rem x y <? 0) (y <? 0)); exact Hd.
Qed.

Theorem modf_spec a b : modf a b = Nm (Z.modulo (unN a) (unN b)).
Proof.
  destruct a as [x], b as [y]. unfold modf, zero. unfold_prims.
  destruct (Z.eqb_spec y 0) as [->|Hy]; [now rewrite Zmod_0_r|].
  destruct (smallb x), (smallb y); cbv beta iota; cbn [unI unN]; try reflexivity.
  rewrite floor_fix_spec. f_equal.
  destruct (quot_rem_floor x y Hy) as [_ Hm].
  destruct (negb (Z.rem x y =? 0) && xorb (Z.rem x y <? 0) (y <? 0)); exact Hm.
Qed.

(** [pow] computes [a ^ b] when the exponent is a [u32], and also for an
    exponent beyond it when the base is [0] or [1]; any other exponent
    beyond [u32] panics in Rust. *)
Theorem pow_spec a b : 0 <= unN b ->
  (unN b <= 4294967295 \/ unN a = 0 \/ unN a = 1) ->
  pow a b = Nm (unN a ^ unN b).
Proof.
  destruct a as [x], b as [e]. cbn [unN]. intros He Hr. unfold pow. unfold_prims.
  assert (Hpow01 : x = 0 \/ x = 1 -> 0 < e -> Nm x = Nm (x ^ e)).
  { intros [-> | ->] Hp; f_equal; [now rewrite Z.pow_0_l | now rewrite Z.pow_1_l]. }
  destruct (smallb e) eqn:Hse; cbv beta iota; cbn [unI unN].
  - destruct (Z.ltb_spec e 0); [lia|]. destruct (Z.ltb_spec 4294967295 e).
    + apply Hpow01; lia.
    + destruct (smallb x); cbv beta iota; cbn [unI unN]; [|reflexivity].
      now destruct (in_i64b (x ^ e)).
  - apply smallb_false in Hse. unfold small in Hse. apply Hpow01; lia.
Qed.

Theorem leb_spec a b : leb a b = Z.leb (unN a) (unN b).
Proof.
  destruct a as [x], b as [y]. unfold leb, num_compare. simpl.
  destruct (Z.compare_spec x y); symmetry; [apply Z.leb_le | apply Z.leb_le | apply Z.leb_gt]; lia.
Qed.

Theorem ltb_spec a b : ltb a b = Z.ltb (unN a) (unN b).
Proof.
  destruct a as [x], b as [y]. unfold ltb, num_compare. simpl.
  destruct (Z.compare_spec x y); symmetry; [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Theorem min_spec a b : min a b = Nm (Z.min (unN a) (unN b)).
Proof.
  unfold min. rewrite leb_spec. destruct a as [x], b as [y]. simpl.
  destruct (Z.leb_spec x y); f_equal; lia.
Qed.

Theorem max_spec a b : max a b = Nm (Z.max (unN a) (unN b)).
Proof.
  unfold max. rewrite leb_spec. destruct a as [x], b as [y]. simpl.
  destruct (Z.leb_spec y x); f_equal; lia.
Qed.

Theorem clamp_spec lo r : clamp lo r = Nm (Z.max (unN lo) (unN r)).
Proof.
  unfold clamp. rewrite ltb_spec. destruct lo as [l], r as [x]. simpl.
  destruct (Z.ltb_spec x l); f_equal; lia.
Qed.

Theorem eqb_spec a b : num_eqb a b = Z.eqb (unN a) (unN b).
Proof. reflexivity. Qed.

Theorem compare_spec a b : num_compare a b = Z.compare (unN a) (unN b).
Proof. reflexivity. Qed.

(** ** The fast paths stay in range and keep the representation canonical *)

Lemma in_i64_enc s : in_i64 (2 * s + 1) <-> small s.
Proof. unfold in_i64, small. lia. Qed.

Lemma in_i64_double s : in_i64 (2 * s) <-> small s.
Proof. unfold in_i64, small. lia. Qed.

(** On two small numbers, [num_word b - 1] does not overflow, and the word
    [r] that the checked addition returns is odd and decodes to a small
    number, the precondition of [num_of_word]. *)
Theorem add_fast_ok x y r : small x -> small y ->
  in_i64 (2 * y + 1 - 1) /\
  (i_checked_add (num_word (Nm x)) (i_sub (num_word (Nm y)) i_1) = ISome r ->
   Z.odd (unI r) = true /\ small (Z.shiftr (unI r) 1)).
Proof.
  intros Hx Hy. split; [unfold in_i64, small in *; lia|].
  unfold_prims. replace (2 * x + 1 + (2 * y + 1 - 1)) with (2 * (x + y) + 1) by lia.
  destruct (in_i64b (2 * (x + y) + 1)) eqn:Hs; [|discriminate].
  intros Hr. assert (r = I (2 * (x + y) + 1)) as -> by congruence. cbn [unI]. rewrite shiftr_enc. split.
  - rewrite Z.add_comm, Z.odd_add_mul_2. reflexivity.
  - apply in_i64b_spec, in_i64_enc in Hs. exact Hs.
Qed.

Theorem sub_fast_ok x y r : small x -> small y ->
  in_i64 (2 * y + 1 - 1) /\
  (i_checked_sub (num_word (Nm x)) (i_sub (num_word (Nm y)) i_1) = ISome r ->
   Z.odd (unI r) = true /\ small (Z.shiftr (unI r) 1)).
Proof.
  intros Hx Hy. split; [unfold in_i64, small in *; lia|].
  unfold_prims. replace (2 * x + 1 - (2 * y + 1 - 1)) with (2 * (x - y) + 1) by lia.
  destruct (in_i64b (2 * (x - y) + 1)) eqn:Hs; [|discriminate].
  intros Hr. assert (r = I (2 * (x - y) + 1)) as -> by congruence. cbn [unI]. rewrite shiftr_enc. split.
  - rewrite Z.add_comm, Z.odd_add_mul_2. reflexivity.
  - apply in_i64b_spec, in_i64_enc in Hs. exact Hs.
Qed.

(** [num_word a - 1] does not overflow, and [r + 1] neither: [r] is even. *)
Theorem mul_fast_ok x y r : small x -> small y ->
  in_i64 (2 * x + 1 - 1) /\
  (i_checked_mul (i_sub (num_word (Nm x)) i_1) (i_shr1 (num_word (Nm y))) = ISome r ->
   in_i64 (unI r + 1) /\ Z.odd (unI r + 1) = true /\ small (Z.shiftr (unI r + 1) 1)).
Proof.
  intros Hx Hy. split; [unfold in_i64, small in *; lia|].
  unfold_prims. rewrite shiftr_enc.
  replace ((2 * x + 1 - 1) * y) with (2 * (x * y)) by lia.
  destruct (in_i64b (2 * (x * y))) eqn:Hs; [|discriminate].
  intros Hr. assert (r = I (2 * (x * y))) as -> by congruence. cbn [unI]. apply in_i64b_spec, in_i64_double in Hs.
  rewrite shiftr_enc. split; [|split].
  - unfold in_i64, small in *. lia.
  - rewrite Z.add_comm, Z.odd_add_mul_2. reflexivity.
  - exact Hs.
Qed.

(** Negation and absolute value of a small number do not overflow. *)
Theorem neg_abs_fast_ok x : small x -> in_i64 (- x) /\ in_i64 (Z.abs x).
Proof. unfold small, in_i64. lia. Qed.

(** Floor division of two small numbers, the divisor non-zero: no overflow
    in [/], [%] or the correction. *)
Theorem divf_fast_ok x y : small x -> small y -> y <> 0 ->
  in_i64 (Z.quot x y) /\ in_i64 (Z.quot x y - 1).
Proof.
  intros Hx Hy H0.
  assert (Habs : Z.abs (Z.quot x y) <= Z.abs x).
  { rewrite <- Z.quot_abs by exact H0. rewrite Z.quot_div_nonneg by lia.
    apply Z.div_le_upper_bound; [lia|]. nia. }
  unfold small, in_i64 in *. lia.
Qed.

(** The floor remainder of two small numbers is small, so [modf] builds it
    with [num_S]; the correction [r + y] does not overflow. *)
Theorem modf_fast_ok x y : small x -> small y -> y <> 0 ->
  in_i64 (Z.rem x y + y) /\ small (Z.modulo x y).
Proof.
  intros Hx Hy H0. split.
  - pose proof (Z.rem_bound_abs x y H0). unfold small, in_i64 in *. lia.
  - unfold small in *. destruct (Z.ltb_spec 0 y).
    + pose proof (Z.mod_pos_bound x y ltac:(lia)). lia.
    + pose proof (Z.mod_neg_bound x y ltac:(lia)). lia.
Qed.

(** ** The remap table *)

Definition of_nat (n : nat) : num := Nm (Z.of_nat n).
Definition of_pos (p : positive) : num := Nm (Z.pos p).
Definition of_N (n : N) : num := Nm (Z.of_N n).
Definition of_Z (z : Z) : num := Nm z.

Ltac num_ok := rewrite ?add_spec, ?sub_spec, ?mul_spec, ?neg_spec, ?abs_spec,
  ?divf_spec, ?modf_spec, ?min_spec, ?max_spec, ?clamp_spec, ?leb_spec, ?ltb_spec;
  cbn [unN].

Section nat_table.
  Variables n m : nat.
  Lemma nat_add_ok : add (of_nat n) (of_nat m) = of_nat (n + m).
  Proof. unfold of_nat. num_ok. f_equal. lia. Qed.
  Lemma nat_mul_ok : mul (of_nat n) (of_nat m) = of_nat (n * m).
  Proof. unfold of_nat. num_ok. f_equal. lia. Qed.
  Lemma nat_sub_ok : sub0 (of_nat n) (of_nat m) = of_nat (n - m).
  Proof. unfold sub0, of_nat, zero. num_ok. unfold num_S, i_0. cbn [unI unN]. f_equal. lia. Qed.
  Lemma nat_eqb_ok : num_eqb (of_nat n) (of_nat m) = Nat.eqb n m.
  Proof.
    unfold of_nat, num_eqb. simpl. destruct (Z.eqb_spec (Z.of_nat n) (Z.of_nat m)), (Nat.eqb_spec n m); lia.
  Qed.
  Lemma nat_leb_ok : leb (of_nat n) (of_nat m) = Nat.leb n m.
  Proof. unfold of_nat. num_ok. destruct (Z.leb_spec (Z.of_nat n) (Z.of_nat m)), (Nat.leb_spec n m); lia. Qed.
  Lemma nat_ltb_ok : ltb (of_nat n) (of_nat m) = Nat.ltb n m.
  Proof. unfold of_nat. num_ok. destruct (Z.ltb_spec (Z.of_nat n) (Z.of_nat m)), (Nat.ltb_spec n m); lia. Qed.
  Lemma nat_compare_ok : num_compare (of_nat n) (of_nat m) = Nat.compare n m.
  Proof. unfold of_nat, num_compare. simpl. apply Nat2Z.inj_compare. Qed.
  Lemma nat_max_ok : max (of_nat n) (of_nat m) = of_nat (Nat.max n m).
  Proof. unfold of_nat. num_ok. f_equal. lia. Qed.
  Lemma nat_min_ok : min (of_nat n) (of_nat m) = of_nat (Nat.min n m).
  Proof. unfold of_nat. num_ok. f_equal. lia. Qed.
  Lemma nat_div_ok : divf (of_nat n) (of_nat m) = of_nat (Nat.div n m).
  Proof. unfold of_nat. num_ok. f_equal. symmetry. apply Nat2Z.inj_div. Qed.
  Lemma nat_modulo_ok : modf (of_nat n) (of_nat m) = of_nat (Nat.modulo n m).
  Proof. unfold of_nat. num_ok. f_equal. symmetry. apply Nat2Z.inj_mod. Qed.
  Lemma nat_pow_ok : Z.of_nat m <= 4294967295 \/ n = 0%nat \/ n = 1%nat ->
    pow (of_nat n) (of_nat m) = of_nat (Nat.pow n m).
  Proof.
    intros H. unfold of_nat. rewrite pow_spec by (cbn [unN]; lia). cbn [unN]. f_equal.
    symmetry. apply Nat2Z.inj_pow.
  Qed.
  Lemma nat_succ_ok : succ (of_nat n) = of_nat (S n).
  Proof. unfold succ, of_nat, one. num_ok. unfold num_S, i_1. cbn [unI unN]. f_equal. lia. Qed.
End nat_table.

Section pos_table.
  Variables p q : positive.
  Lemma pos_add_ok : add (of_pos p) (of_pos q) = of_pos (p + q).
  Proof. unfold of_pos. num_ok. reflexivity. Qed.
  Lemma pos_succ_ok : succ (of_pos p) = of_pos (Pos.succ p).
  Proof. unfold succ, of_pos, one. num_ok. unfold num_S, i_1. cbn [unI unN]. f_equal. lia. Qed.
  Lemma pos_pred_ok : pred1 (of_pos p) = of_pos (Pos.pred p).
  Proof.
    unfold pred1, of_pos, one. num_ok. unfold num_S, i_1. cbn [unI unN]. f_equal.
    destruct (Pos.eq_dec p 1) as [->|H]; [reflexivity|].
    rewrite Pos2Z.inj_pred by exact H.
    assert (Z.pos p <> 1) by (intros E; apply H; now injection E). lia.
  Qed.
  Lemma pos_sub_ok : sub1 (of_pos p) (of_pos q) = of_pos (p - q).
  Proof.
    unfold sub1, of_pos, one. num_ok. unfold num_S, i_1. cbn [unI unN]. f_equal.
    rewrite Pos2Z.inj_sub_max. reflexivity.
  Qed.
  Lemma pos_mul_ok : mul (of_pos p) (of_pos q) = of_pos (p * q).
  Proof. unfold of_pos. num_ok. reflexivity. Qed.
  Lemma pos_min_ok : min (of_pos p) (of_pos q) = of_pos (Pos.min p q).
  Proof. unfold of_pos. num_ok. f_equal. symmetry. apply Pos2Z.inj_min. Qed.
  Lemma pos_max_ok : max (of_pos p) (of_pos q) = of_pos (Pos.max p q).
  Proof. unfold of_pos. num_ok. f_equal. symmetry. apply Pos2Z.inj_max. Qed.
  Lemma pos_eqb_ok : num_eqb (of_pos p) (of_pos q) = Pos.eqb p q.
  Proof. reflexivity. Qed.
  Lemma pos_compare_ok : num_compare (of_pos p) (of_pos q) = Pos.compare p q.
  Proof. reflexivity. Qed.
  Lemma pos_onebit_ok : double_plus_one (of_pos p) = of_pos (xI p).
  Proof. unfold double_plus_one, of_pos, one, two. num_ok. unfold num_S, i_1, i_2. cbn [unI unN]. f_equal. lia. Qed.
  Lemma pos_zerobit_ok : double (of_pos p) = of_pos (xO p).
  Proof. unfold double, of_pos, two. num_ok. unfold num_S, i_2. cbn [unI unN]. f_equal. lia. Qed.
End pos_table.

Section N_table.
  Variables n m : N.
  Lemma N_add_ok : add (of_N n) (of_N m) = of_N (n + m).
  Proof. unfold of_N. num_ok. f_equal. lia. Qed.
  Lemma N_succ_ok : succ (of_N n) = of_N (N.succ n).
  Proof. unfold succ, of_N, one. num_ok. unfold num_S, i_1. cbn [unI unN]. f_equal. lia. Qed.
  Lemma N_pred_ok : pred0 (of_N n) = of_N (N.pred n).
  Proof. unfold pred0, of_N, zero, one. num_ok. unfold num_S, i_0, i_1. cbn [unI unN]. f_equal. lia. Qed.
  Lemma N_sub_ok : sub0 (of_N n) (of_N m) = of_N (n - m).
  Proof. unfold sub0, of_N, zero. num_ok. unfold num_S, i_0. cbn [unI unN]. f_equal. lia. Qed.
  Lemma N_mul_ok : mul (of_N n) (of_N m) = of_N (n * m).
  Proof. unfold of_N. num_ok. f_equal. lia. Qed.
  Lemma N_div_ok : divf (of_N n) (of_N m) = of_N (N.div n m).
  Proof. unfold of_N. num_ok. f_equal. symmetry. apply N2Z.inj_div. Qed.
  Lemma N_modulo_ok : modf (of_N n) (of_N m) = of_N (N.modulo n m).
  Proof. unfold of_N. num_ok. f_equal. symmetry. apply N2Z.inj_mod. Qed.
  Lemma N_min_ok : min (of_N n) (of_N m) = of_N (N.min n m).
  Proof. unfold of_N. num_ok. f_equal. lia. Qed.
  Lemma N_max_ok : max (of_N n) (of_N m) = of_N (N.max n m).
  Proof. unfold of_N. num_ok. f_equal. lia. Qed.
  Lemma N_eqb_ok : num_eqb (of_N n) (of_N m) = N.eqb n m.
  Proof.
    unfold of_N, num_eqb. simpl. destruct (Z.eqb_spec (Z.of_N n) (Z.of_N m)), (N.eqb_spec n m); lia.
  Qed.
  Lemma N_compare_ok : num_compare (of_N n) (of_N m) = N.compare n m.
  Proof. unfold of_N, num_compare. simpl. apply N2Z.inj_compare. Qed.
End N_table.

Section Z_table.
  Variables z w : Z.
  Lemma Z_add_ok : add (of_Z z) (of_Z w) = of_Z (z + w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_succ_ok : succ (of_Z z) = of_Z (Z.succ z).
  Proof. unfold succ, of_Z, one. num_ok. reflexivity. Qed.
  Lemma Z_pred_ok : pred (of_Z z) = of_Z (Z.pred z).
  Proof. unfold pred, of_Z, one. num_ok. reflexivity. Qed.
  Lemma Z_sub_ok : sub (of_Z z) (of_Z w) = of_Z (z - w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_mul_ok : mul (of_Z z) (of_Z w) = of_Z (z * w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_opp_ok : neg (of_Z z) = of_Z (Z.opp z).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_min_ok : min (of_Z z) (of_Z w) = of_Z (Z.min z w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_max_ok : max (of_Z z) (of_Z w) = of_Z (Z.max z w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_eqb_ok : num_eqb (of_Z z) (of_Z w) = Z.eqb z w.
  Proof. reflexivity. Qed.
  Lemma Z_div_ok : divf (of_Z z) (of_Z w) = of_Z (Z.div z w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_modulo_ok : modf (of_Z z) (of_Z w) = of_Z (Z.modulo z w).
  Proof. unfold of_Z. num_ok. reflexivity. Qed.
  Lemma Z_compare_ok : num_compare (of_Z z) (of_Z w) = Z.compare z w.
  Proof. reflexivity. Qed.
  Lemma Z_of_N_ok (n : N) : id (of_N n) = of_Z (Z.of_N n).
  Proof. reflexivity. Qed.
  Lemma Z_abs_N_ok : abs (of_Z z) = of_N (Z.abs_N z).
  Proof. unfold of_Z, of_N. num_ok. f_equal. symmetry. apply N2Z.inj_abs_N. Qed.
  Lemma Z_fromneg_ok (p : positive) : neg (of_pos p) = of_Z (Z.neg p).
  Proof. unfold of_pos, of_Z. num_ok. reflexivity. Qed.
End Z_table.
