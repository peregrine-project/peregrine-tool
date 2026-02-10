import LeanToLambdaBox

inductive Bool_ where
  | false : Bool_
  | true : Bool_

inductive Nat_ where
  | zero : Nat_
  | suc : Nat_ -> Nat_

inductive List_ (A : Type) where
  | empty : List_ A
  | cons : A -> List_ A -> List_ A

def add (x y : Nat_) : Nat_ :=
  match x with
  | .zero => y
  | .suc x => .suc (add x y)

def times (x y : Nat_) : Nat_ :=
  match x with
  | .zero => y
  | .suc x => add y (times x y)

def and (a b : Bool_) : Bool_ :=
  match a with
  | .false => .false
  | .true => b

def or (a b : Bool_) : Bool_ :=
  match a with
  | .false => b
  | .true => .true

def test : List_ Bool_ :=
  .cons .true (.cons .false (.cons .true (.cons .false .empty)))



#erase test to "extraction/Demo.ast"
