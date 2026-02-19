module Unicode where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

s⇒o₁ : List Nat → List Nat
s⇒o₁ _ = 1 ∷ []

main : List Nat
main = s⇒o₁ (1 ∷ 2 ∷ 3 ∷ [])
{-# COMPILE AGDA2LAMBOX main #-}
