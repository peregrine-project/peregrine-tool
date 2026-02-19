data Bool : Set where
  false true : Bool

case : {A : Set} → Bool → (Bool → A) → A
case b f = f b

not : Bool → Bool
not x = case x λ where
  true  → false
  false → true

test : Bool
test = not true
{-# COMPILE AGDA2LAMBOX test #-}
