module Irr where

open import Agda.Builtin.Nat

infixr 7 _∷_
data Vec (A : Set) : @0 Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

map : ∀ {A B : Set} {@0 n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

xs : Vec Nat 2
xs = 1 ∷ 0 ∷ []

ys : Vec Nat 2
ys = map suc xs
{-# COMPILE AGDA2LAMBOX ys #-}
