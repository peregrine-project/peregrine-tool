(** * Quicksort Benchmark

    Functional quicksort using list partitioning.
    Classic divide-and-conquer sorting algorithm.

    Uses Uint63 for integer elements.
*)

From Stdlib Require Import List Arith.
Import ListNotations.

(* Lean implementation of tail recursive append *)
Fixpoint reverseAux {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | a::l => reverseAux l (a :: l2)
  end.
Definition reverse {A : Type} (l : list A) : list A :=
  reverseAux l [].
Definition appendTR {A : Type} (l1 l2 : list A) : list A :=
  reverseAux (reverse l1) l2.

(** Partition a list into elements < pivot and elements >= pivot *)
Fixpoint partition (pivot : nat) (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
      let (lo, hi) := partition pivot xs in
      if x <? pivot then (x :: lo, hi) else (lo, x :: hi)
  end.

(** Quicksort with fuel for termination *)
Fixpoint quicksort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l  (* Out of fuel, return unsorted *)
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | pivot :: rest =>
          let (lo, hi) := partition pivot rest in
          appendTR (quicksort_fuel fuel' lo)  (appendTR [pivot] (quicksort_fuel fuel' hi))
      end
  end.

(** Quicksort with sufficient fuel *)
Definition quicksort (l : list nat) : list nat :=
  quicksort_fuel (length l * length l) l.

Fixpoint divmod (x y u : nat) : nat :=
  match x with
  | O => u
  | S x' =>
    match u with
    | O => divmod x' y y
    | S u' => divmod x' y u'
    end
  end.

Definition modulo (x y : nat) : nat :=
  match y with
  | O => x
  | S y' => y' - (divmod x y' y')
  end.

(** Generate a pseudo-random list for testing *)
Fixpoint make_list_aux (seed : nat) (fuel : nat) (acc : list nat) : list nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      let next := modulo (12 + (49 * seed)) 214 in
      make_list_aux next fuel' (next :: acc)
  end.

Definition make_list (n : nat) : list nat :=
  make_list_aux 42 n [].

(** Check if a list is sorted *)
Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as rest) =>
    if (x <=? y) then is_sorted rest else false
  end.

(** Benchmark: sort 1000 random elements, return length if sorted *)
Definition quicksort_bench (n : nat) : nat :=
  let l := make_list n in
  let sorted := quicksort l in
  if is_sorted sorted then length sorted else 0.

From Peregrine.Plugin Require Import Loader.

Peregrine Extract "ast/Quicksort.ast" quicksort_bench.
Peregrine Extract Typed "ast/Quicksort_typed.ast" quicksort_bench.
