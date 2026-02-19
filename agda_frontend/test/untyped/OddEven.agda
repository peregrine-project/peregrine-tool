data Bool : Set where false true : Bool

not : Bool -> Bool
not true  = false
not false = true

notnot : Bool → Bool
notnot b = not (not b)

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

double : Nat -> Nat
double zero = zero
double (succ n) = succ (succ (double n))

odd even : Nat -> Bool

odd zero = false
odd (succ n) = even n

even zero = true
even (succ n) = odd n

test : Bool
test = odd (succ (succ zero))
{-# COMPILE AGDA2LAMBOX test #-}

record Pair (A : Set) (B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
