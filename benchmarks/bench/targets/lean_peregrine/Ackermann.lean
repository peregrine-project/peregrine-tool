/-
  Ackermann Function Benchmark - Extraction for Peregrine
  A(0, n) = n + 1
  A(m, 0) = A(m-1, 1)
  A(m, n) = A(m-1, A(m, n-1))
-/
import LeanToLambdaBox

partial def ackermann (m n : Nat) : Nat :=
  match m with
  | 0 => n + 1
  | m' + 1 =>
    match n with
    | 0 => ackermann m' 1
    | n' + 1 => ackermann m' (ackermann m n')

-- Benchmark instances
def ackermann_3_9 : Nat := ackermann 3 9
def ackermann_3_10 : Nat := ackermann 3 10
def ackermann_3_11 : Nat := ackermann 3 11

-- Extract to LambdaBox AST
#erase ackermann_3_9 to "extracted/ackermann_3_9.ast"
#erase ackermann_3_10 to "extracted/ackermann_3_10.ast"
#erase ackermann_3_11 to "extracted/ackermann_3_11.ast"
