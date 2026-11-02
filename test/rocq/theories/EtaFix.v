(* Top-level fixpoints that are eta-applied to the outer binders, in the two
   shapes where a parameter of the fixpoint cannot alias the outer binder. *)

(* The body refers to [x], which the recursive call must not rebind. *)
Definition capture (x : nat) : nat :=
  (fix f (y : nat) : nat :=
     match y with
     | O => x
     | S n => f n
     end) x.

(* Two arguments, but one parameter: the fixpoint returns a function. *)
Definition over (x y : nat) : nat :=
  (fix f (a : nat) : nat -> nat :=
     match a with
     | O => fun b => b
     | S n => fun b => S (f n b)
     end) x y.

Definition test : nat :=
  capture 3 + over 2 3.
