(** * Binary Trees Benchmark

    From the Computer Language Benchmarks Game.
    Allocate and deallocate many binary trees.

    https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/binarytrees.html
*)

From Stdlib Require Import List.
Import ListNotations.

(** Binary tree with integer items *)
Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

(** Create a complete binary tree of given depth *)
Fixpoint make (depth : nat) : tree :=
  match depth with
  | O => Leaf
  | S d => Node (make d) 0%nat (make d)
  end.

(** Check (compute checksum of) a tree by summing nodes *)
Fixpoint check (t : tree) : nat :=
  match t with
  | Leaf => 0%nat
  | Node l _ r => (1 + check l + check r)%nat
  end.

(** Create a tree of given depth and immediately check it *)
Definition make_check (depth : nat) : nat :=
  check (make depth).

(** The stretch tree: make a tree one deeper than max and check it *)
Definition stretch_tree (max_depth : nat) : nat :=
  make_check (S max_depth).

(** Long-lived tree: kept around during the benchmark *)
Definition long_lived_tree (max_depth : nat) : tree :=
  make max_depth.

(** Run iterations at a given depth *)
Fixpoint run_iterations (iterations : nat) (depth : nat) (acc : nat) : nat :=
  match iterations with
  | O => acc
  | S n => run_iterations n depth (make_check depth + acc)%nat
  end.

Fixpoint pow (m n : nat) : nat :=
  match n with
  | O => 1
  | S n => (pow m n) * m
  end.

(** Calculate number of iterations: 2^(max_depth - depth + min_depth) *)
Definition calc_iterations (max_depth depth min_depth : nat) : nat :=
  Nat.pow 2 (max_depth - depth + min_depth).
  (* pow (max_depth - depth + min_depth). *)

(** Run benchmark for depths from min_depth to max_depth, stepping by 2 *)
(** fuel controls termination *)
Fixpoint run_depths_aux (fuel : nat) (min_depth current_depth max_depth : nat) (acc : list nat) : list nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb current_depth max_depth then
        let iterations := calc_iterations max_depth current_depth min_depth in
        let result := run_iterations iterations current_depth 0%nat in
        run_depths_aux fuel' min_depth (2 + current_depth) max_depth (result :: acc)
      else
        acc
  end.

Definition run_depths (min_depth max_depth : nat) : list nat :=
  run_depths_aux (S max_depth) min_depth min_depth max_depth [].

Fixpoint sum_depths (depths : list nat) : nat :=
  match depths with
  | [] => 0
  | x :: xs => x + sum_depths xs
  end.

(** Main benchmark function
    n = input parameter (typically 10-21)
    Returns: (stretch_check, depth_results, long_lived_check)
*)
Definition binary_trees_main (n : nat) : nat * list nat * nat :=
  let min_depth := 4 in
  let max_depth := Nat.max (2 + min_depth) n in
  let stretch := stretch_tree max_depth in
  let long_tree := long_lived_tree max_depth in
  let depth_results := run_depths min_depth max_depth in
  let long_check := check long_tree in
  (stretch, depth_results, long_check).

(** Simplified benchmark: just return the stretch tree check for small n *)
Definition binary_trees_simple (n : nat) : nat :=
  let '(stretch, depths, long_check) := binary_trees_main n in
  (stretch + long_check + sum_depths depths)%nat.

From Peregrine.Plugin Require Import Loader.

Peregrine Extract "ast/BinaryTrees.ast" binary_trees_simple.
Peregrine Extract Typed "ast/BinaryTrees_typed.ast" binary_trees_simple.
