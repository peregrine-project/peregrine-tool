{-# OPTIONS --erasure #-}
module MainFannkuch where

open import Prelude
open import Haskell
open import Fannkuch

main : IO ⊤
main = do
  n ← getInput 10
  -- log the result (i.e. force evaluation)
  putStrLn $ showNat $ fannkuchBench n
