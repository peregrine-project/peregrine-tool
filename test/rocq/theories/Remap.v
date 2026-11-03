(* Constants remapped by the configuration files of the Lean and F# tests: an
   axiom, and a definition whose body must not be used. *)
Axiom ext_id : nat -> nat.

Definition shadowed (n : nat) : nat := 0.

Definition test : nat :=
  shadowed (ext_id 3).
