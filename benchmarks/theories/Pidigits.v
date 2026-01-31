(** * Pidigits Benchmark

    From the Computer Language Benchmarks Game.
    Streaming arbitrary-precision arithmetic.

    https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/pidigits.html

    Uses the unbounded spigot algorithm by Rabinowitz and Wagon,
    as improved by Gibbons.
*)

From Stdlib Require Import ZArith List.
From BenchmarksGame Require Import Common.
Import ListNotations.

Open Scope Z_scope.

(** Linear fractional transformation (LFT) represented as matrix
    | q r |
    | s t |
    Represents the function x -> (q*x + r) / (s*x + t)
*)
Record lft : Type := mkLft {
  lft_q : Z;
  lft_r : Z;
  lft_s : Z;
  lft_t : Z
}.

(** Compose two LFTs (matrix multiplication) *)
Definition compose (a b : lft) : lft :=
  mkLft
    (lft_q a * lft_q b + lft_r a * lft_s b)
    (lft_q a * lft_r b + lft_r a * lft_t b)
    (lft_s a * lft_q b + lft_t a * lft_s b)
    (lft_s a * lft_r b + lft_t a * lft_t b).

(** Extract a digit from an LFT *)
Definition extr (z : lft) (x : Z) : Z :=
  (lft_q z * x + lft_r z) / (lft_s z * x + lft_t z).

(** The k-th term in the series *)
Definition lfts (k : Z) : lft :=
  mkLft k (4 * k + 2) 0 (2 * k + 1).

(** Check if we can safely extract a digit *)
Definition safe (z : lft) (n : Z) : bool :=
  Z.eqb n (extr z 4).

(** Produce: extract digit and update state *)
Definition prod (z : lft) (n : Z) : lft :=
  compose (mkLft 10 (-10 * n) 0 1) z.

(** Consume: incorporate next term *)
Definition cons (z : lft) (zk : lft) : lft :=
  compose z zk.

(** Initial state *)
Definition init : lft := mkLft 1 0 0 1.

(** Generate n digits of pi *)
Fixpoint stream_aux (fuel : nat) (z : lft) (k : Z) (n_digits : nat) (acc : list Z) : list Z :=
  match fuel, n_digits with
  | O, _ => rev acc  (* Out of fuel *)
  | _, O => rev acc  (* Done generating digits *)
  | S fuel', S nd =>
    let y := extr z 3 in
    if safe z y then
      (* Safe to extract digit y *)
      stream_aux fuel' (prod z y) k nd (y :: acc)
    else
      (* Need more terms *)
      let k' := k + 1 in
      stream_aux fuel' (cons z (lfts k')) k' (S nd) acc
  end.

Definition stream (n_digits : nat) : list Z :=
  stream_aux (10 * n_digits) init 0 n_digits [].

(** Convert digits to a single large number for verification *)
Fixpoint digits_to_Z (digits : list Z) (acc : Z) : Z :=
  match digits with
  | [] => acc
  | d :: ds => digits_to_Z ds (acc * 10 + d)
  end.

(** Main benchmark function
    n = number of digits to compute
    Returns list of digits
*)
Definition pidigits_main (n : nat) : list Z :=
  stream n.

(** Get digits as a single integer *)
Definition pidigits_number (n : nat) : Z :=
  digits_to_Z (stream n) 0.

(** Test: first 10 digits of pi should be 3141592653 *)
Definition test_pidigits : list Z := pidigits_main 10.

(** Smaller test: first 5 digits *)
Definition test_pidigits_small : list Z := pidigits_main 5.

Close Scope Z_scope.
