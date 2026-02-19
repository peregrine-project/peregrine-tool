-- {-# OPTIONS --level-universe #-}
open import Agda.Builtin.Nat using (Nat; suc)

open import Agda.Primitive

-- ** level definitions should be ignored
0ℓ : Level
0ℓ = lzero

mkLevel : Nat → Level
mkLevel 0 = 0ℓ
mkLevel (suc n) = lsuc (mkLevel n)

-- ** level function arguments should be erased
testLevel : Level → Nat
testLevel _ = 42

-- ** level application arguments should be erased
testMkLevel : Nat
testMkLevel = testLevel (mkLevel 42)
{-# COMPILE AGDA2LAMBOX testMkLevel #-}

-- ** level record fields should be erased
record SomeLvl : Set where
  constructor this
  field ℓ : Level
open SomeLvl public

someLvl : SomeLvl
someLvl = this 0ℓ

lvlToNat : Level → Nat
lvlToNat _ = 42

testSomeLvl : Nat
testSomeLvl = lvlToNat (someLvl .ℓ)
{-# COMPILE AGDA2LAMBOX testSomeLvl #-}

constLvl : ∀ {A : Set} → A → Level → A
constLvl x _ = x

testConstLvl : Nat
testConstLvl = constLvl 42 (someLvl .ℓ)
{-# COMPILE AGDA2LAMBOX testConstLvl #-}

const : ∀ {A B : Set} → A → B → A
const x _ = x

testConst : Nat
testConst = const 42 0
{-# COMPILE AGDA2LAMBOX testConst #-}

testConstLvl2 : Nat
testConstLvl2 = const 42 (someLvl .ℓ)
{-# COMPILE AGDA2LAMBOX testConstLvl2 #-}

testWhere : Nat
testWhere = toNat (someLvl .ℓ)
  where
  toNat : Level → Nat
  toNat _ = 42
{-# COMPILE AGDA2LAMBOX testWhere #-}
