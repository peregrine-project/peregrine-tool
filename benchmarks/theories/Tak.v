(** * Tak (Takeuchi) Function Benchmark

    The Tak function is a classic benchmark for function call overhead.
    Originally defined with integers, we use nat with an offset.

    tak(x, y, z) = if x <= y then z
                   else tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y))

    Uses Z for signed integers.
*)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

(** Tak function with fuel for termination *)
Fixpoint tak_fuel (fuel : nat) (x y z : Z) : Z :=
  match fuel with
  | O => 0  (* Out of fuel *)
  | S fuel' =>
      if x <=? y then z
      else tak_fuel fuel'
             (tak_fuel fuel' (x - 1) y z)
             (tak_fuel fuel' (y - 1) z x)
             (tak_fuel fuel' (z - 1) x y)
  end.

(** Tak with sufficient fuel *)
Definition tak (x y z : Z) : Z :=
  tak_fuel (Z.to_nat (x * y * z + 1000)) x y z.

(** Test values:
    tak(6, 3, 0) = ?
    tak(12, 8, 4) = ?
    tak(18, 12, 6) = 7
*)
Definition test_tak_small : Z := tak 6 3 0.
Definition test_tak_medium : Z := tak 12 8 4.

(** Benchmark: tak(18, 12, 6) *)
Definition tak_bench : Z := tak 18 12 6.

(** Larger benchmark: tak(24, 16, 8) *)
Definition tak_bench_large : Z := tak 24 16 8.
