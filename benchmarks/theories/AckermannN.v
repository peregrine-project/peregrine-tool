(** * Ackermann Function Benchmark (nat -> nat -> N version)

    Uses nat for arguments and recursion structure (efficient Peano matching).
    Returns N (binary) for the result.

    Type: nat -> nat -> N

    This is the natural hybrid approach:
    - m and n are small (e.g., 3 and 11)
    - The result can be large (e.g., 16381 for A(3,11))
    - Intermediate values that become arguments are bounded by the final result
*)

From Stdlib Require Import NArith PeanoNat.

(** Internal ackermann using nat throughout *)
Fixpoint ackermann_nat (m : nat) : nat -> nat :=
  match m with
  | O => S
  | S m' =>
      fix ack_m (n : nat) : nat :=
        match n with
        | O => ackermann_nat m' 1
        | S n' => ackermann_nat m' (ack_m n')
        end
  end.

(** Public interface returning N *)
Definition ackermann (m n : nat) : N := N.of_nat (ackermann_nat m n).

(** Benchmarks - arguments are nat, result is N *)
Definition ackermann_n_3_9 : N := ackermann 3 9.
Definition ackermann_n_3_10 : N := ackermann 3 10.
Definition ackermann_n_3_11 : N := ackermann 3 11.
