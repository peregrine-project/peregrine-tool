{-# OPTIONS --erasure #-}

module Quicksort where

open import Prelude

-- NOTE: if_then_else_ not properly handled by agda2lambox
partitionAux : Bool → Nat → List Nat → List Nat → (List Nat × List Nat)
partitionAux true  x lo hi = x ∷ lo , hi
partitionAux false x lo hi = lo , x ∷ hi

partition : Nat -> List Nat -> (List Nat × List Nat)
partition _ [] = ([] , [])
partition pivot (x ∷ xs) with partition pivot xs
... | (lo , hi) = partitionAux (x < pivot) x lo hi


quicksortFuel : Nat -> List Nat -> List Nat
quicksortFuel 0 l = l
quicksortFuel _ [] = []
quicksortFuel _ (x ∷ []) = (x ∷ [])
quicksortFuel (suc fuel) (pivot ∷ rest) with partition pivot rest
... | (lo , hi) = appendTR (quicksortFuel fuel lo) (appendTR [ pivot ] (quicksortFuel fuel hi))

quicksort : List Nat -> List Nat
quicksort l =
  quicksortFuel (length l * length l) l

makeListAux : Nat -> Nat -> List Nat -> List Nat
makeListAux _ 0 acc = acc
makeListAux seed (suc fuel) acc with mod (12 + (49 * seed)) 214
... | next = makeListAux next fuel (next ∷ acc)

makeList : Nat -> List Nat
makeList n =
  makeListAux 42 n []

{-# TERMINATING #-}
isSorted : List Nat -> Bool
isSorted [] = true
isSorted (x ∷ []) = true
isSorted (x ∷ (y ∷ rest)) with (x < (1 + y))
... | false = false
... | true  = isSorted (y ∷ rest)

quicksortBenchAux : Bool → List Nat → Nat
quicksortBenchAux true  xs = length xs
quicksortBenchAux false xs = 0

quicksortBenchAuxAux : List Nat -> Nat
quicksortBenchAuxAux ss = quicksortBenchAux (isSorted ss) ss

quicksortBench : Nat -> Nat
quicksortBench n = quicksortBenchAuxAux (quicksort (makeList n))
{-# COMPILE AGDA2LAMBOX quicksortBench #-}
