(* A fixpoint eta-applied to its first parameter and to a proof, with the
   structural argument after the proof.  --lbox-opts hoists the fixpoint and
   drops the dead proof parameter, so the index of the structural argument
   must move down by one. *)

Definition g (x : nat) : nat -> nat :=
  (fix F (x : nat) (H : True) (m : nat) {struct m} : nat :=
     match m with
     | O => x
     | S m' => S (F x H m')
     end) x I.

Definition test : nat := g 3 4.
