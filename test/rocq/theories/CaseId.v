(* A match that rebuilds the constructor with an erased field in place of the
   pattern variable is not an identity case: the scrutinee's field is a
   number, the result's field a proof.  --lbox-case-id must leave it alone
   (the typed Rust code would not type-check otherwise). *)

Definition f (o : option nat) : option True :=
  match o with
  | None => None
  | Some _ => Some I
  end.

Definition test : nat :=
  match f (Some 5) with
  | Some _ => 1
  | None => 0
  end.
