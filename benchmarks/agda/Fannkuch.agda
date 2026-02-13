{-# OPTIONS --erasure #-}
{-
  Fannkuch Redux Benchmark
  From the Computer Language Benchmarks Game
  Indexed-access to tiny integer-sequence

  Purely functional implementation using immutable lists
-}

module Fannkuch where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Prelude

-- Reverse the first n elements of a list, keeping the rest

reversePrefix : Nat → List Nat → List Nat
reversePrefix n l = aux n l []
  where
    aux : Nat → List Nat → List Nat → List Nat
    aux 0       xs       acc = acc ++ xs
    aux (suc n) []       acc = acc
    aux (suc n) (x ∷ xs) acc = aux n xs (x ∷ acc)


private
  @0 _ : reversePrefix 3 (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 5 ∷ []
  _ = refl

-- One flip operation: reverse prefix of length = first element + 1
flip : List Nat → List Nat
flip []           = []
flip perm@(x ∷ _) = reversePrefix (suc x) perm

{-# TERMINATING  #-}
-- Count flips until first element is 0
countFlips : List Nat → Nat
countFlips = aux 0
  where
    aux : Nat → List Nat → Nat
    aux count []      = count
    aux count (0 ∷ _) = count
    aux count perm    = aux (suc count) (flip perm)

-- Rotate first n elements: [a, b, c, d, ...] -> [b, c, d, a, ...]
rotatePrefix : List Nat → Nat → List Nat
rotatePrefix [] n = []
rotatePrefix xs 0 = xs
rotatePrefix xs 1 = xs
rotatePrefix (x ∷ xs) (suc n) =
  let (rest , suffix) = splitAt n xs
  in rest ++ [ x ] ++ suffix

-- Find the index i where count[i] < i
findI : List Nat → Maybe Nat
findI = findIndex (λ i x → x < i)

-- Reset counts from 0 to i-1 to 0
resetCounts : List Nat → Nat → List Nat
resetCounts []       _       = []
resetCounts xs       zero    = xs
resetCounts (x ∷ xs) (suc i) = 0 ∷ resetCounts xs i

-- Generate next permutation using Heap's algorithm variant
nextPerm : List Nat → List Nat → Maybe (List Nat × List Nat)
nextPerm perm counts with findI counts
... | nothing = nothing
... | just i  =
  let perm'    = rotatePrefix perm (suc i)
      counts'  = updateAt suc counts i
      counts'' = resetCounts counts' i
  in just (perm' , counts'')

{-# TERMINATING #-}
fannkuchLoop : List Nat → List Nat → Nat → Nat
fannkuchLoop perm counts maxFlips =
  let flips     = countFlips perm
      maxFlips' = max maxFlips flips
  in case nextPerm perm counts of λ where
    nothing → maxFlips'
    (just (perm' , counts')) → fannkuchLoop perm' counts' maxFlips'

fannkuch : Nat → Nat
fannkuch n =
  let perm   = range n
      counts = replicate n 0
  in fannkuchLoop perm counts 0

fannkuchBench : Nat → Nat
fannkuchBench n = fannkuch n

{-
private
  -- sanity check implementation
  _ : fannkuch 7 ≡ 16
  _ = refl
  _ : fannkuch 8 ≡ 22
  _ = refl
  _ : fannkuch 9 ≡ 30
  _ = refl
-- -}
