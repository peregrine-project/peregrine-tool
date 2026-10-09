(* Mutual fixpoint under section variables: once the section is closed,
   [A], [k] and [d] are parameters outside the fixpoint block. *)
Section Closure.
  Variable A : Type.
  Variable k : nat.
  Variable d : A.

  Fixpoint walk (n : nat) : nat :=
    match n with
    | O => k
    | S n => S (step n d)
    end
  with step (n : nat) (x : A) : nat :=
    match n with
    | O => S k
    | S n => walk n
    end.
End Closure.

Definition test : nat :=
  walk nat (S (S O)) O (S (S (S O))).
