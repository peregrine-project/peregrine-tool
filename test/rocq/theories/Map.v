(* open import Agda.Builtin.Nat using (Nat; suc; zero) *)
(* open import Agda.Builtin.List *)
From Stdlib Require Import List.

Import ListNotations.


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Definition xs : list nat :=
  [1;3;5].

Definition ys : list nat :=
  map double xs.
