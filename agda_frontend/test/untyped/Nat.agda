open import Agda.Builtin.Nat

thing : Nat
thing = 1 + 2
{-# COMPILE AGDA2LAMBOX thing #-}

