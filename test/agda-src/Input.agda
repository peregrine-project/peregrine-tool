-- The flags of agda2lambox's test library
{-# OPTIONS --no-projection-like --erasure --prop #-}
-- agda2lambox's test/untyped/Input.agda, with an entry point whose result
-- can be printed
open import Agda.Builtin.Equality

data Bool : Set where
  false true : Bool

and : Bool -> Bool -> Bool
and false _ = false
and true  y = y

not : Bool -> Bool
not false = true
not true  = false

record Export : Set where
  field
    ad : Bool → Bool → Bool
    nt : Bool → Bool
open Export public

test : Export
test = record
  { ad = and
  ; nt = not
  }

-- The record of functions cannot be printed: the test checks this digest of
-- it, and (not false) (not (and true false)) = true
observe : Export → Bool
observe e = ad e (nt e false) (nt e (ad e true false))

digest : Bool
digest = observe test
{-# COMPILE AGDA2LAMBOX digest #-}

_ : test ≡ record { ad = and ; nt = not }
_ = refl

_ : digest ≡ true
_ = refl
