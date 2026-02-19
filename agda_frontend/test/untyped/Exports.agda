module Exports where

open import Agda.Builtin.Nat

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

main : Exports
main = record
  { eone   = one
  ; etwo   = two
  ; ethree = three
  ; efour  = four
  }
{-# COMPILE AGDA2LAMBOX main #-}
