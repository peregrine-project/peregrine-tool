data Bool : Set where
  false true : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data List (A : Set) : Set where
  empty : List A
  cons  : A → List A → List A

add : Nat → Nat → Nat
add zero y = y
add (suc x) y = suc (add x y)

times : Nat → Nat → Nat
times zero y = zero
times (suc x) y = add y (times x y)

and : Bool → Bool → Bool
and false _ = false
and true  b = b

or : Bool → Bool → Bool
or true _  = true
or false b = b

test : List Bool
test = cons true (cons false (cons true (cons false empty)))
{-# COMPILE AGDA2LAMBOX test #-}
