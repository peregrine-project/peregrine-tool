(** * Treesort Benchmark

    Sorting by inserting elements into a binary search tree,
    then flattening the tree with an in-order traversal.

    Uses Uint63 for integer elements.
*)

From Stdlib Require Import List Uint63 ZArith.
Import ListNotations.

Open Scope uint63_scope.

(** Binary search tree *)
Inductive bst : Type :=
  | Leaf : bst
  | Node : bst -> int -> bst -> bst.

(** Insert a value into the BST *)
Fixpoint insert (x : int) (t : bst) : bst :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l v r =>
      if x <? v then Node (insert x l) v r
      else if v <? x then Node l v (insert x r)
      else t  (* duplicate, keep as is *)
  end.

(** Build a BST from a list *)
Definition build_tree (l : list int) : bst :=
  fold_left (fun t x => insert x t) l Leaf.

(** In-order traversal (flattens to sorted list) *)
Fixpoint inorder (t : bst) : list int :=
  match t with
  | Leaf => []
  | Node l v r => inorder l ++ [v] ++ inorder r
  end.

(** Treesort: build tree then flatten *)
Definition treesort (l : list int) : list int :=
  inorder (build_tree l).

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
Definition test_treesort_small : list int :=
  treesort [5; 2; 8; 1; 9; 3; 7; 4; 6; 0].

(** Count nodes in tree (measure tree size) *)
Fixpoint tree_size (t : bst) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + tree_size l + tree_size r
  end.

(** Benchmark: sort random list, return length if sorted correctly *)
Definition treesort_bench (n : int) : int :=
  let l := make_list n in
  let sorted := treesort l in
  if is_sorted sorted then of_Z (Z.of_nat (length sorted)) else 0.
