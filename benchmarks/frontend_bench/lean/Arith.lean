import LeanToLambdaBox

def benchArith (n : Nat) : Nat :=
  2 ^ (((n * 3) - n) + 3)


-- Extract to LambdaBox AST
#erase benchArith config {extern := .preferLogical, nat := .peano} to "ast/Arith.ast"
