(** * Fannkuch Redux Benchmark

    From the Computer Language Benchmarks Game.
    Indexed-access to tiny integer-sequence.

    https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/fannkuchredux.html

    The fannkuch benchmark computes the maximum number of "flips" (reversals
    of the prefix) needed to sort a permutation.
*)

From Stdlib Require Import List ZArith Lia.
From BenchmarksGame Require Import Common.
Import ListNotations.

(** Reverse the first n elements of a list *)
Fixpoint reverse_prefix_aux {A : Type} (n : nat) (l : list A) (acc : list A) : list A :=
  match n, l with
  | O, _ => acc ++ l
  | S n', x :: xs => reverse_prefix_aux n' xs (x :: acc)
  | S _, [] => acc
  end.

Definition reverse_prefix {A : Type} (n : nat) (l : list A) : list A :=
  reverse_prefix_aux n l [].

(** One flip operation: reverse prefix of length = first element + 1 *)
Definition flip (perm : list nat) : list nat :=
  match perm with
  | [] => []
  | x :: _ => reverse_prefix (S x) perm
  end.

(** Count flips until first element is 0 *)
Fixpoint count_flips_aux (fuel : nat) (perm : list nat) (count : nat) : nat :=
  match fuel with
  | O => count  (* Out of fuel, return current count *)
  | S fuel' =>
    match perm with
    | [] => count
    | 0 :: _ => count  (* Sorted when first element is 0 *)
    | _ => count_flips_aux fuel' (flip perm) (S count)
    end
  end.

Definition count_flips (perm : list nat) : nat :=
  count_flips_aux 1000 perm 0.  (* Fuel = 1000, enough for n <= 12 *)

(** Generate next permutation in lexicographic order (simple version) *)
(* This uses Heap's algorithm idea - rotate the first k elements *)
Fixpoint rotate {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => xs ++ [x]
  end.

(** Generate all permutations using Heap's algorithm *)
Fixpoint heap_permutations_aux (n : nat) (perm : list nat) (counts : list nat)
                                (acc : list (list nat)) : list (list nat) :=
  match n with
  | O => acc
  | S fuel =>
    match counts with
    | [] => acc
    | c :: cs =>
      if Nat.ltb c (length perm) then
        (* Increment count and generate next permutation *)
        let perm' := if Nat.eqb (Nat.modulo (length cs) 2) 0
                     then swap perm 0 c 0
                     else swap perm (length cs) c 0 in
        heap_permutations_aux fuel perm' ((S c) :: cs) (perm' :: acc)
      else
        (* Reset this count and move to next position *)
        heap_permutations_aux fuel perm (0 :: cs) acc
    end
  end.

(** Simple permutation generator: generate all permutations of [0..n-1] *)
(* For simplicity, we use a factorial-based approach *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

(** Insert x at position i in list *)
Fixpoint insert_at {A : Type} (x : A) (i : nat) (l : list A) : list A :=
  match i, l with
  | O, _ => x :: l
  | S i', [] => [x]
  | S i', y :: ys => y :: insert_at x i' ys
  end.

(** Generate all permutations by inserting each element at all positions *)
Fixpoint all_perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    let sub_perms := all_perms xs in
    flat_map (fun p => map (fun i => insert_at x i p) (seq 0 (S (length p)))) sub_perms
  end.

(** Initial permutation [0, 1, 2, ..., n-1] *)
Definition initial_perm (n : nat) : list nat := seq 0 n.

(** Compute maximum flips over all permutations *)
Definition max_flips (perms : list (list nat)) : nat :=
  fold_left Nat.max (map count_flips perms) 0.

(** Compute checksum (alternating sum of flip counts) *)
Fixpoint checksum_aux (perms : list (list nat)) (sign : Z) (acc : Z) : Z :=
  match perms with
  | [] => acc
  | p :: ps => checksum_aux ps (Z.opp sign) (acc + sign * Z.of_nat (count_flips p))%Z
  end.

Definition checksum (perms : list (list nat)) : Z :=
  checksum_aux perms 1%Z 0%Z.

(** Main benchmark function
    n = sequence length (typically 7-12)
    Returns: (checksum, max_flips)
*)
Definition fannkuch_main (n : nat) : Z * nat :=
  let perms := all_perms (initial_perm n) in
  (checksum perms, max_flips perms).

(** Simplified benchmark: just return max_flips for small n *)
Definition fannkuch_simple (n : nat) : nat :=
  let (_, mf) := fannkuch_main n in mf.

(** Test with n=7 (5040 permutations) *)
Definition test_fannkuch : Z * nat := fannkuch_main 7.

(** Smaller test with n=5 *)
Definition test_fannkuch_small : Z * nat := fannkuch_main 5.
