import LeanToLambdaBox

inductive Nat_ where
  | zero : Nat_
  | suc : Nat_ -> Nat_

inductive List_ (A : Type) where
  | empty : List_ A
  | cons : A -> List_ A -> List_ A

def double (n : Nat_) : Nat_ :=
  match n with
  | .zero => .zero
  | .suc n => .suc (.suc (double n))

def map (A B : Type) (f : A -> B) (l : List_ A) : List_ B :=
  match l with
  | .empty => .empty
  | .cons x xs => .cons (f x) (map A B f xs)

def xs : List_ Nat_ :=
  .cons (.suc .zero) (.cons (.suc (.suc (.suc .zero))) (.cons (.suc (.suc (.suc (.suc (.suc .zero))))) .empty))

def ys : List_ Nat_ :=
  map Nat_ Nat_ double xs



#erase ys to "extraction/Map.ast"
