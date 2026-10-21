(* A let-bound polymorphic function used at two types. Rocq's extraction to
   OCaml generalises the let; the type inference for untyped input does not,
   so the typed backends reject the untyped program. *)

Definition test : nat :=
  let id := fun (A : Type) (x : A) => x in
  if id bool true then id nat 2 else 0.
