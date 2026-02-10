Inductive Bool :=
| false
| true.

Inductive Nat :=
| zero
| suc : Nat -> Nat.

Inductive List (A : Type) :=
| empty : List A
| cons : A -> List A -> List A.

Arguments empty {A}.
Arguments cons {A} a l.

Fixpoint add (x y : Nat) : Nat :=
  match x with
  | zero => y
  | suc x => suc (add x y)
  end.

Fixpoint times (x y : Nat) : Nat :=
  match x with
  | zero => zero
  | suc x => add y (times x y)
  end.

Definition and (a b : Bool) : Bool :=
  match a with
  | false => false
  | true => b
  end.

Definition or (a b : Bool) : Bool :=
  match a with
  | true => true
  | false => b
  end.

Definition test : List Bool :=
  cons true (cons false (cons true (cons false empty))).
