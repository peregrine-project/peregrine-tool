-- The flags of agda2lambox's test library
{-# OPTIONS --no-projection-like --erasure --prop #-}
-- agda2lambox's test/untyped/Exports.agda, with an entry point whose result
-- can be printed
module Exports where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

one : Nat
one = 1

two : Nat
two = 2

three : Nat → Nat
three zero = zero
three (suc n) = n

four : Nat → Nat → Nat
four zero m = m
four (suc n) m = suc (four n m)

record Exports : Set where
  field
    eone   : Nat
    etwo   : Nat
    ethree : Nat → Nat
    efour  : Nat → Nat → Nat
open Exports

test : Exports
test = record
  { eone   = one
  ; etwo   = two
  ; ethree = three
  ; efour  = four
  }

-- The record of functions cannot be printed: the test checks this digest of
-- it, efour 1 1 = 2
observe : Exports → Nat
observe e = efour e (ethree e (etwo e)) (eone e)

digest : Nat
digest = observe test
{-# COMPILE AGDA2LAMBOX digest #-}

_ : test ≡ record { eone = 1 ; etwo = 2 ; ethree = three ; efour = four }
_ = refl

_ : digest ≡ 2
_ = refl
