-- The flags of agda2lambox's test library
{-# OPTIONS --no-projection-like --erasure --prop #-}
-- agda2lambox's test/untyped/Irr.agda, with an entry point whose result
-- can be printed
module Irr where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
import Agda.Builtin.List as L

infixr 7 _∷_
data Vec (A : Set) : @0 Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

map : ∀ {A B : Set} {@0 n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

xs : Vec Nat 2
xs = 1 ∷ 0 ∷ []

test : Vec Nat 2
test = map suc xs

-- The constructor _∷_ keeps its erased index as a field, so no driver prints
-- the vector as a list: the test checks the list of its elements
toList : ∀ {A : Set} {@0 n} → Vec A n → L.List A
toList [] = L.[]
toList (x ∷ xs) = x L.∷ toList xs

digest : L.List Nat
digest = toList test
{-# COMPILE AGDA2LAMBOX digest #-}

_ : test ≡ 2 ∷ 1 ∷ []
_ = refl

_ : digest ≡ 2 L.∷ 1 L.∷ L.[]
_ = refl
