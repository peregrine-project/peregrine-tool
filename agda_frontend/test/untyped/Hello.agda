open import Agda.Builtin.Nat
open import Agda.Builtin.List

String : Set
String = List Nat

hello : String
hello = 72 ∷ 101 ∷ 108 ∷ 108 ∷ 111 ∷ 33 ∷ []
{-# COMPILE AGDA2LAMBOX hello #-}
