open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.List

double : Nat → Nat
double zero = zero
double (suc x) = suc (suc (double x))

xs : List Nat
xs = 1 ∷ 3 ∷ 5 ∷ []

map : {A B : Set} -> (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

ys : List Nat
ys = map double xs
{-# COMPILE AGDA2LAMBOX ys #-}
