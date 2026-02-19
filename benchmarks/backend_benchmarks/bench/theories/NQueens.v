(** * N-Queens Benchmark

    Classic backtracking problem: place N queens on an NxN chessboard
    such that no two queens attack each other.

    Uses Uint63 for board positions.
*)

From Stdlib Require Import List Uint63 ZArith.
Import ListNotations.

Open Scope uint63_scope.

(** Check if a queen at column c attacks position (r, c') *)
Definition attacks (c r c' : int) : bool :=
  let diff := if c' <? c then c - c' else c' - c in
  (c =? c') || (diff =? r).

(** Check if placing a queen at row r, column c is safe given existing queens *)
Fixpoint safe_aux (placed : list int) (r c : int) : bool :=
  match placed with
  | [] => true
  | c' :: rest =>
      if attacks c r c' then false
      else safe_aux rest (r + 1) c
  end.

Definition safe (placed : list int) (c : int) : bool :=
  safe_aux placed 1 c.

(** Generate list [0, 1, ..., n-1] *)
Fixpoint range_aux (n : nat) (acc : list int) : list int :=
  match n with
  | O => acc
  | S n' => range_aux n' (of_Z (Z.of_nat n') :: acc)
  end.

Definition range (n : nat) : list int := range_aux n [].

(** Solve N-Queens: return all solutions *)
Fixpoint solve_aux (fuel : nat) (n : nat) (row : nat) (placed : list int) : list (list int) :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.eqb row n then
        [placed]  (* Found a solution *)
      else
        let candidates := filter (fun c => safe placed c) (range n) in
        flat_map (fun c => solve_aux fuel' n (S row) (placed ++ [c])) candidates
  end.

Definition solve (n : nat) : list (list int) :=
  solve_aux (Nat.pow 2 (n * n)) n 0 [].

(** Count solutions *)
Definition nqueens (n : nat) : nat :=
  length (solve n).

(** Test: nqueens 8 should be 92 *)
Definition test_nqueens_8 : nat := nqueens 8.

(** Smaller test: nqueens 4 should be 2 *)
Definition test_nqueens_4 : nat := nqueens 4.
