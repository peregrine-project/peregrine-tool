/-
  Tak (Takeuchi) Function Benchmark - Extraction for Peregrine
  tak(x, y, z) = if x <= y then z
                 else tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y))
-/
import LeanToLambdaBox

partial def tak (x y z : Int) : Int :=
  if x <= y then z
  else tak (tak (x - 1) y z) (tak (y - 1) z x) (tak (z - 1) x y)

-- Benchmark instances
def tak_18_12_6 : Int := tak 18 12 6
def tak_21_14_7 : Int := tak 21 14 7
def tak_24_16_8 : Int := tak 24 16 8

-- Extract to LambdaBox AST
#erase tak_18_12_6 to "extracted/tak_18_12_6.ast"
#erase tak_21_14_7 to "extracted/tak_21_14_7.ast"
#erase tak_24_16_8 to "extracted/tak_24_16_8.ast"
