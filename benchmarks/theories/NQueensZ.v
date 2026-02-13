(** * N-Queens Benchmark (Z-based)

    Classic backtracking problem: place N queens on an NxN chessboard
    such that no two queens attack each other.

    Uses Z for board positions (no Uint63 primitives).
*)

From Stdlib Require Import List ZArith.
Import ListNotations.

Open Scope Z_scope.

(** Check if a queen at column c attacks position (r, c') *)
Definition attacks (c r c' : Z) : bool :=
  let diff := Z.abs (c' - c) in
  (c =? c') || (diff =? r).

(** Check if placing a queen at row r, column c is safe given existing queens *)
Fixpoint safe_aux (placed : list Z) (r c : Z) : bool :=
  match placed with
  | [] => true
  | c' :: rest =>
      if attacks c r c' then false
      else safe_aux rest (r + 1) c
  end.

Definition safe (placed : list Z) (c : Z) : bool :=
  safe_aux placed 1 c.

(** Generate list [0, 1, ..., n-1] as Z values *)
Fixpoint range_aux (n : nat) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => range_aux n' (Z.of_nat n' :: acc)
  end.

Definition range (n : nat) : list Z := range_aux n [].

(** Length as Z for efficient fuel computation *)
Fixpoint length_Z {A : Type} (l : list A) : Z :=
  match l with
  | [] => 0
  | _ :: xs => 1 + length_Z xs
  end.

(** Solve N-Queens with nat fuel (fuel decreases structurally) *)
Fixpoint solve_fuel (fuel : nat) (n : nat) (row : nat) (placed : list Z) : list (list Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.eqb row n then
        [placed]  (* placed is in reverse order, but that's fine for counting *)
      else
        let candidates := filter (fun c => safe placed c) (range n) in
        (* Use cons to prepend: most recent queen at head for safe_aux *)
        flat_map (fun c => solve_fuel fuel' n (S row) (c :: placed)) candidates
  end.

(** Solve with sufficient fuel based on n *)
Definition solve (n : nat) : list (list Z) :=
  (* Fuel: n+1 is enough since we recurse once per row *)
  solve_fuel (S n) n 0 [].

(** Count solutions *)
Definition nqueens (n : nat) : nat :=
  length (solve n).

(** Return count as Z for benchmarking *)
Definition nqueens_z (n : nat) : Z :=
  length_Z (solve n).

(** Test: nqueens 8 should be 92 *)
Definition test_nqueens_8 : nat := nqueens 8.

(** Benchmarks *)
Definition nqueens_z_8 : Z := nqueens_z 8.
Definition nqueens_z_10 : Z := nqueens_z 10.
Definition nqueens_z_11 : Z := nqueens_z 11.
