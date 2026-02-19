open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat

test : List Bool
test = true ∷ false ∷ []

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

test2 : List Nat
test2 = map (5 +_) (1 ∷ [])
{-# COMPILE AGDA2LAMBOX test2 #-}
