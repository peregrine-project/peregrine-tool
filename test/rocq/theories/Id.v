(* Corelib declares [id : ID] through the alias [ID := forall A, A -> A];
   typed extraction must still give [id] a type parameter
   (benchmarks UPSTREAM_ISSUES entry 3) *)
From Stdlib Require Import List.

Import ListNotations.

Definition test : list nat :=
  id [1;2].
