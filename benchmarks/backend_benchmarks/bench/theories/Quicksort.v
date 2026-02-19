(** * Quicksort Benchmark

    Functional quicksort using list partitioning.
    Classic divide-and-conquer sorting algorithm.

    Uses Uint63 for integer elements.
*)

From Stdlib Require Import List Uint63 ZArith.
Import ListNotations.

Open Scope uint63_scope.

(** Partition a list into elements < pivot and elements >= pivot *)
Fixpoint partition (pivot : int) (l : list int) : list int * list int :=
  match l with
  | [] => ([], [])
  | x :: xs =>
      let (lo, hi) := partition pivot xs in
      if x <? pivot then (x :: lo, hi) else (lo, x :: hi)
  end.

(** Quicksort with fuel for termination *)
Fixpoint quicksort_fuel (fuel : nat) (l : list int) : list int :=
  match fuel with
  | O => l  (* Out of fuel, return unsorted *)
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | pivot :: rest =>
          let (lo, hi) := partition pivot rest in
          quicksort_fuel fuel' lo ++ [pivot] ++ quicksort_fuel fuel' hi
      end
  end.

(** Quicksort with sufficient fuel *)
Definition quicksort (l : list int) : list int :=
  quicksort_fuel (length l * length l) l.

(** Generate a pseudo-random list for testing *)
Fixpoint make_list_aux (seed : int) (fuel : nat) (acc : list int) : list int :=
  match fuel with
  | O => acc
  | S fuel' =>
      let next := (seed * 1103515245 + 12345) mod 2147483648 in
      make_list_aux next fuel' (next :: acc)
  end.

Definition make_list (n : int) : list int :=
  make_list_aux 42 (Z.to_nat (to_Z n)) [].

(** Check if a list is sorted *)
Fixpoint is_sorted (l : list int) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as rest) => (x <=? y) && is_sorted rest
  end.

(** Test: sort a small list *)
Definition test_quicksort_small : list int :=
  quicksort [5; 2; 8; 1; 9; 3; 7; 4; 6; 0].

(** Benchmark: sort 1000 random elements, return length if sorted *)
Definition quicksort_bench (n : int) : int :=
  let l := make_list n in
  let sorted := quicksort l in
  if is_sorted sorted then of_Z (Z.of_nat (length sorted)) else 0.
