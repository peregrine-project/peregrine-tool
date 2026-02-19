module EtaCon where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

addone : Nat → Nat
addone = suc

cons : {A : Set} → A → List A → List A
cons = _∷_

example : List Nat
example = cons 1 []
{-# COMPILE AGDA2LAMBOX example #-}