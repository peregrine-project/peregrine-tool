Inductive Bool :=
| false
| true.

Definition not (b : Bool) : Bool :=
  match b with
  | false => true
  | true => false
  end.

Definition notnot (b : Bool) : Bool :=
  not (not b).

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Fixpoint odd (n : nat) : Bool :=
  match n with
  | O => false
  | S n => even n
  end
with even (n : nat) : Bool :=
  match n with
  | O => true
  | S n => odd n
  end.

Definition test : Bool :=
  odd (S (S O)).
