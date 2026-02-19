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

main : Export
main = record
  { ad = and
  ; nt = not
  }
{-# COMPILE AGDA2LAMBOX main #-}

