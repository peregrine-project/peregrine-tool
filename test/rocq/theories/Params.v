(* Inductive parameters that are not type variables of the extracted type:
   a value parameter, a Prop parameter, and a phantom type parameter. *)

Record Tagged (n : nat) := mkTagged { payload : nat }.

Definition two : {x : nat | 0 < x} := exist _ 2 (le_S _ _ (le_n 1)).

Inductive Proxy (A : Type) : Type := proxy : Proxy A.

Definition fromTagged (t : Tagged 3) : nat := payload 3 t.

Definition fromSig (p : {x : nat | 0 < x}) : nat := proj1_sig p.

Definition fromProxy {A} (p : Proxy A) : nat := match p with proxy _ => 1 end.

Definition test : nat :=
  fromTagged (mkTagged 3 1) + fromSig two + fromProxy (proxy nat).
