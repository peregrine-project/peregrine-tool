Inductive Even :=
| zero : Even
| succ : Odd -> Even
with Odd :=
| succ' : Even -> Odd.

Fixpoint oddNat (n : Odd) : nat :=
  match n with
  | succ' e => S (evenNat e)
  end
with evenNat (n : Even) : nat :=
  match n with
  | zero => O
  | succ o => S (oddNat o)
  end.

Definition test : nat :=
  oddNat (succ' zero).
