module _ where

K : {A B : Set} → A → B → A
K = λ a b → a
{-# COMPILE AGDA2LAMBOX K #-}
