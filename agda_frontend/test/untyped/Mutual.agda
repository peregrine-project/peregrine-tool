data Odd  : Set
data Even : Set

data Even where
  zero : Even
  succ : Odd → Even

data Odd where
  succ : Even → Odd

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

oddNat  : Odd → Nat
evenNat : Even → Nat

oddNat (succ e) = succ (evenNat e)

evenNat zero = zero
evenNat (succ o) = succ (oddNat o)

test : Nat
test = oddNat (succ zero)
{-# COMPILE AGDA2LAMBOX test #-}
