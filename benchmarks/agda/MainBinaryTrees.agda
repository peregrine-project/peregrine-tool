module MainBinaryTrees where

open import Prelude
open import Haskell
open import BinaryTrees

main : IO ⊤
main = do
  n ← getInput 10
  -- log the result (i.e. force evaluation)
  putStrLn $ showNat $ binaryTreesBench n
