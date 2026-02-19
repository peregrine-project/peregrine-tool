{-# OPTIONS --erasure #-}

module Arith where

open import Prelude

benchArith : Nat -> Nat
benchArith n = pow2 (3 + ((3 * n) - n))


{-# COMPILE AGDA2LAMBOX benchArith #-}
