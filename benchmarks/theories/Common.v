(** * Common utilities for Benchmarks Game *)

From Stdlib Require Import List ZArith String Ascii.
Import ListNotations.

(** Natural number iteration *)
Fixpoint nat_iter {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n' => f (nat_iter n' f x)
  end.

(** Generate a list [0, 1, ..., n-1] *)
Fixpoint seq (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq (S start) len'
  end.

(** Sum of a list of nats *)
Fixpoint sum_nat (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_nat xs
  end.

(** Sum of a list of Z *)
Fixpoint sum_Z (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: xs => (x + sum_Z xs)%Z
  end.

(** Map with index *)
Fixpoint mapi_aux {A B : Type} (f : nat -> A -> B) (i : nat) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f i x :: mapi_aux f (S i) xs
  end.

Definition mapi {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
  mapi_aux f 0 l.

(** Repeat a value n times *)
Fixpoint repeat {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => x :: repeat x n'
  end.

(** Update list at index *)
Fixpoint update {A : Type} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: xs, O => x :: xs
  | y :: xs, S i' => y :: update xs i' x
  end.

(** Get element at index with default *)
Fixpoint nth_default {A : Type} (default : A) (l : list A) (i : nat) : A :=
  match l, i with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S i' => nth_default default xs i'
  end.

(** Swap elements at indices i and j *)
Definition swap {A : Type} (l : list A) (i j : nat) (default : A) : list A :=
  let xi := nth_default default l i in
  let xj := nth_default default l j in
  update (update l i xj) j xi.
