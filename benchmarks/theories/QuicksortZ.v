(** * Quicksort Benchmark (Z version)

    Functional quicksort using list partitioning.
    Uses Z for integer elements (no Uint63 primitives).
    Uses fuel pattern with efficient Z-based fuel computation.
*)

From Stdlib Require Import List ZArith.
Import ListNotations.

Open Scope Z_scope.

(** Partition a list into elements < pivot and elements >= pivot *)
Fixpoint partition (pivot : Z) (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | x :: xs =>
      let (lo, hi) := partition pivot xs in
      if x <? pivot then (x :: lo, hi) else (lo, x :: hi)
  end.

(** Quicksort with fuel for termination *)
Fixpoint quicksort_fuel (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l  (* Out of fuel, return as-is *)
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | pivot :: rest =>
          let (lo, hi) := partition pivot rest in
          quicksort_fuel fuel' lo ++ [pivot] ++ quicksort_fuel fuel' hi
      end
  end.

(** Compute length using Z for efficiency, then convert to nat once *)
Fixpoint length_Z {A : Type} (l : list A) : Z :=
  match l with
  | [] => 0
  | _ :: xs => 1 + length_Z xs
  end.

(** Quicksort with efficiently computed fuel *)
Definition quicksort (l : list Z) : list Z :=
  quicksort_fuel (Z.to_nat (length_Z l)) l.

(** Generate a pseudo-random list for testing using LCG *)
Fixpoint make_list_aux (seed : Z) (fuel : nat) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      let next := (seed * 1103515245 + 12345) mod 2147483648 in
      make_list_aux next fuel' (next :: acc)
  end.

Definition make_list (n : Z) : list Z :=
  make_list_aux 42 (Z.to_nat n) [].

(** Check if a list is sorted *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as rest) => (x <=? y) && is_sorted rest
  end.

(** Benchmark: sort n random elements, return length if sorted *)
Definition quicksort_bench_z (n : Z) : Z :=
  let l := make_list n in
  let sorted := quicksort l in
  if is_sorted sorted then length_Z sorted else 0.

(** Test cases *)
Definition test_quicksort_small : list Z :=
  quicksort [5; 2; 8; 1; 9; 3; 7; 4; 6; 0].

Definition quicksort_z_10 : Z := quicksort_bench_z 10.
Definition quicksort_z_100 : Z := quicksort_bench_z 100.
Definition quicksort_z_500 : Z := quicksort_bench_z 500.
Definition quicksort_z_1000 : Z := quicksort_bench_z 1000.
