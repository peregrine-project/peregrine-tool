(* A match on a constructor applied to bound variables: instance specialization
   reduces it, and must keep the two arguments apart. *)
Definition pick (x y : nat) : nat :=
  match (x, y) with
  | (a, b) => a - b
  end.

Definition test : nat :=
  pick 5 2.
