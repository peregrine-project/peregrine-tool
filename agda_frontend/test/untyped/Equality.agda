open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

private variable ℓ : Level

eqzero : 0 ≡ 0
eqzero = refl

private variable A B C : Set ℓ

cong : ∀ {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

EqNat = _≡_ {A = Nat}

eqOne : EqNat 1 1
eqOne = cong suc eqzero

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

infixr 9 _∘_
infixr -1 _$_

_∘_ : (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

_$_ : (A → B) → A → B
f $ x = f x

eqTwo : EqNat 2 2
eqTwo = sym $ cong (suc ∘ suc) eqzero

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

subst : ∀ {P : A → Set} {a b : A} → a ≡ b → P a → P b
subst refl p = p

add : Nat → Nat → Nat
add zero    y = y
add (suc x) y = suc (add x y)

add-left-id : (a : Nat) → EqNat (add zero a) a
add-left-id zero = refl
add-left-id (suc a) = cong suc $ add-left-id a

suc-left-add : (a b : Nat) → add (suc a) b ≡ suc (add a b)
suc-left-add a zero = refl
suc-left-add a (suc b) = refl

eqLevel : lzero ≡ lzero
eqLevel = refl

toNat : ∀ {x y : Nat} → x ≡ y → Nat
toNat {x = x} {y = .x} refl = x

test : Nat
test = toNat $ suc-left-add 1 0
{-# COMPILE AGDA2LAMBOX test #-}
