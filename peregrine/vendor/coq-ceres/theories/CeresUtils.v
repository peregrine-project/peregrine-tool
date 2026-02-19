(* begin hide *)
From Stdlib Require Import
  List.
Import ListNotations.
(* end hide *)

(** * Functions *)

Definition map_sum {A B B' : Type} (f : B -> B') (x : A + B) : A + B' :=
  match x with
  | inl a => inl a
  | inr b => inr (f b)
  end.

(** Find an element by key in an association list. *)
Fixpoint _find_or {A B C} (eqb : A -> A -> bool) (a : A) (xs : list (A * B)) (f : B -> C) (b : C) : C :=
  match xs with
  | nil => b
  | (x, y) :: xs => if eqb a x then f y else _find_or eqb a xs f b
  end.

(** The bind of the [sum A] monad. *)
Definition _bind_sum {A B C} (x : A + B) (f : B -> A + C) : A + C :=
  match x with
  | inl a => inl a
  | inr b => f b
  end.

(** * Lemmas *)

Lemma app_cons_assoc {A} (xs : list A) (x : A) (ys : list A)
  : xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  rewrite <- app_assoc; reflexivity.
Qed.
