-- compilation of λ□ type schemes
module SchemeTyped where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

data Eq {A : Set} (x : A) : A -> Prop where
  rfl : Eq x x

record Σ (A : Set) (B : A → Prop) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
Σ-syntax : (A : Set) (B : A → Prop) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = [ x ∈ A ∣ B ]

-- NOTE: this doesn't compile properly?
-- the snd projection is compiled while it shouldn't be?
-- record Σ0 (A : Set) (@0 B : A → Set) : Set where
--   constructor _,_
--   field
--     fst    : A
--     @0 snd : B fst

-- expected: type scheme
-- ­ vars: [a, b]
-- ­ type: a → b
Arrow : (A B : Set) → Set
Arrow A B = A → B

-- expected: type scheme
-- - vars: [a]
-- - type: List a
ListAlias : Set → Set
ListAlias = List

ListAlias' : Set → Set
ListAlias' A = List A

-- Rocq-like vectors --

-- expected: type scheme
-- - vars: [a, n]
-- - type: Σ (List a) □
Vec : (A : Set) → Nat → Set
Vec A n = [ xs ∈ List A ∣ Eq (length xs) n ]

Bad : Bool → Set
Bad false = Nat
Bad true  = Bool
