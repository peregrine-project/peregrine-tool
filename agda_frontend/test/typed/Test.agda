module _ where

variable a b : Set

-- ** Datatypes & functions

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

not' : Bool → Bool
not' = λ where
  true  → false
  false → true

{-
not'' : Bool → Bool
not'' = go where go = λ where
  true  → false
  false → true

not''' : Bool → Bool
not''' = M.go where module M where go = λ where
  true  → false
  false → true
  -}

module _ (a : Set) where data Maybe : Set where
  nothing : Maybe
  just    : a → Maybe

fromMaybe : a → Maybe a → a
fromMaybe def = λ where
  nothing  → def
  (just a) → a

{-
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

data Exp (v : Set) : Set where
  Plus : Exp v → Exp v → Exp v
  Int  : Nat → Exp v
  Var  : v → Exp v

eval : (a → Nat) → Exp a → Nat
eval env (Plus a b) = eval env a + eval env b
eval env (Int n) = n
eval env (Var x) = env x

-- ** mutual recursion

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

mutual
  f : ℕ → ℕ
  f Z     = Z
  f (S n) = S (g n)

  g : ℕ → ℕ
  g Z     = Z
  g (S n) = S (S (f n))

open import Agda.Builtin.List using (List; []; _∷_)

-- ** Natural numbers

sum : List Nat → Nat
sum []       = 0
sum (x ∷ xs) = x + sum xs

-- ** Polymorphic functions

_++_ : List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : (a → b) → List a → List b
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- ** Lambdas

plus3 : List Nat → List Nat
plus3 = map (λ n → n + 3)

doubleLambda : Nat → Nat → Nat
doubleLambda = λ a b → a + 2 * b
-}
