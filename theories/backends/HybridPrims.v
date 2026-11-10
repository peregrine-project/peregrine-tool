(** * The primitives of the [rust-hybrid] number runtime

    [HybridRuntime.v] writes the arithmetic of [rust-hybrid] in Rocq; this file
    gives the primitives it is written against.  Each primitive is remapped to
    one line of Rust ([HybridRuntimeRemaps.v]), and its Rocq body here is its
    model over [Z]: the trusted claim is that the Rust line computes the body.

    - [i64] is Rust's [i64], [oi64] its [Option<i64>].  [i_checked_*] are
      [checked_*]; the other operations ([i_sub], [i_add], [i_quot], ...) are
      the plain Rust operators, used only where [HybridRuntime.v] proves that
      they do not overflow and divide by no zero.
    - [num] is [Num<'a>], one tagged word: [2v+1] for a small [v] in
      [-2^62, 2^62), otherwise the address of a GMP integer; the model is the
      integer it denotes.  The representation is canonical (a value in the
      small range is always small), an invariant of the Rust kernel
      [mod __hybrid] that the runtime keeps: [HybridRuntime.v] proves that
      [num_S] and [num_of_word], which build small numbers without a check,
      only receive small values and odd words.
    - [big_*] are the GMP slow paths: compute on [rug::Integer] references to
      the arguments, then build the canonical [num] of the result. *)

From Stdlib Require Import Bool ZArith.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** Ranges *)

Notation P62 := 4611686018427387904%Z (only parsing).
Notation P63 := 9223372036854775808%Z (only parsing).

Definition small (v : Z) : Prop := - P62 <= v <= P62 - 1.
Definition smallb (v : Z) : bool := (- P62 <=? v) && (v <=? P62 - 1).
Definition in_i64 (w : Z) : Prop := - P63 <= w <= P63 - 1.
Definition in_i64b (w : Z) : bool := (- P63 <=? w) && (w <=? P63 - 1).

(** ** [i64] and [Option<i64>] *)

Inductive i64 := I (z : Z).
Definition unI (w : i64) : Z := match w with I z => z end.

Inductive oi64 := ISome (w : i64) | INone.

(** [checked_*]: [Some] of the exact result when it is an [i64]. *)
Definition checked (s : Z) : oi64 := if in_i64b s then ISome (I s) else INone.

Definition i_checked_add (a b : i64) : oi64 := checked (unI a + unI b).
Definition i_checked_sub (a b : i64) : oi64 := checked (unI a - unI b).
Definition i_checked_mul (a b : i64) : oi64 := checked (unI a * unI b).
(** [x.checked_pow(e as u32)], for [0 <= e <= u32::MAX]. *)
Definition i_checked_pow (x e : i64) : oi64 := checked (unI x ^ unI e).

Definition i_add (a b : i64) : i64 := I (unI a + unI b).
Definition i_sub (a b : i64) : i64 := I (unI a - unI b).
Definition i_neg (a : i64) : i64 := I (- unI a).
Definition i_abs (a : i64) : i64 := I (Z.abs (unI a)).
(** [a >> 1], arithmetic. *)
Definition i_shr1 (a : i64) : i64 := I (Z.shiftr (unI a) 1).
(** Rust's truncating [/] and [%]. *)
Definition i_quot (a b : i64) : i64 := I (Z.quot (unI a) (unI b)).
Definition i_rem (a b : i64) : i64 := I (Z.rem (unI a) (unI b)).
Definition i_eqb (a b : i64) : bool := Z.eqb (unI a) (unI b).
Definition i_ltb (a b : i64) : bool := Z.ltb (unI a) (unI b).

Definition i_0 : i64 := I 0.
Definition i_1 : i64 := I 1.
Definition i_2 : i64 := I 2.
Definition i_u32max : i64 := I 4294967295.

(** ** [Num<'a>] *)

Inductive num := Nm (z : Z).
Definition unN (n : num) : Z := match n with Nm z => z end.

(** [a.small()]: the value of a small number. *)
Definition num_small (n : num) : oi64 := if smallb (unN n) then ISome (I (unN n)) else INone.
(** [a.0 & b.0 & 1 == 1]: both numbers are small. *)
Definition num_both_small (a b : num) : bool := smallb (unN a) && smallb (unN b).
(** [a.0], the word of a small number. *)
Definition num_word (n : num) : i64 := I (2 * unN n + 1).
(** [Num(w, _)] for an odd word [w]: the small number [w >> 1]. *)
Definition num_of_word (w : i64) : num := Nm (Z.shiftr (unI w) 1).
(** [Num::S(v)] for a small [v]. *)
Definition num_S (v : i64) : num := Nm (unI v).
(** [self.__int(v)]: the canonical number of any [i64]. *)
Definition num_int (v : i64) : num := Nm (unI v).

(** [PartialEq] and [Ord] of [Num], which use canonicity. *)
Definition num_eqb (a b : num) : bool := Z.eqb (unN a) (unN b).
Definition num_compare (a b : num) : comparison := Z.compare (unN a) (unN b).

(** ** GMP slow paths *)

Definition big_add (a b : num) : num := Nm (unN a + unN b).
Definition big_sub (a b : num) : num := Nm (unN a - unN b).
Definition big_mul (a b : num) : num := Nm (unN a * unN b).
Definition big_neg (a : num) : num := Nm (- unN a).
Definition big_abs (a : num) : num := Nm (Z.abs (unN a)).
(** [div_floor] and [rem_floor], for a non-zero divisor. *)
Definition big_divf (a b : num) : num := Nm (Z.div (unN a) (unN b)).
Definition big_modf (a b : num) : num := Nm (Z.modulo (unN a) (unN b)).
(** [a.pow(e as u32)], for [0 <= e <= u32::MAX]. *)
Definition big_pow (a : num) (e : i64) : num := Nm (unN a ^ unI e).
(** An exponent outside [u32]: [0] and [1] to that power are themselves,
    anything else panics.  The model covers [0] and [1] only. *)
Definition pow_out_of_range (a : num) : num := a.
