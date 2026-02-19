{-# OPTIONS --erasure #-}

module Sieve where

open import Prelude

rangeFromAux : Nat -> Nat -> List Nat -> List Nat
rangeFromAux start 0 acc = acc
rangeFromAux start (suc n') acc
  with start < (start + n' + 1)
... | true =
      rangeFromAux start n' ((start + n') ∷ acc)
... | false = acc

rangeFrom : Nat -> Nat -> List Nat
rangeFrom start limit
  with start < (limit + 1)
... | true =
      rangeFromAux start (limit - start) []
... | false = []

filter : (A -> Bool) -> List A -> List A
filter f [] = []
filter f (x ∷ xs)
  with f x
... | true =
        x ∷ (filter f xs)
... | false = filter f xs

negb : Bool -> Bool
negb false = true
negb true = false

orb : Bool -> Bool -> Bool
orb true _ = true
orb false b = b

removeMultiples : Nat -> List Nat -> List Nat
removeMultiples p l =
  filter (λ n → orb (negb ((mod n p) == 0)) (n == p)) l

sieveAux : Nat -> List Nat -> List Nat -> List Nat
sieveAux 0 candidates primes = appendTR primes candidates
sieveAux (suc n) [] primes = primes
sieveAux (suc n) (p ∷ rest) primes =
  sieveAux n (removeMultiples p rest) (appendTR primes [ p ])

sieve : Nat -> List Nat
sieve n = sieveAux n (rangeFrom 2 (suc n)) []

countPrimes : Nat -> Nat
countPrimes n = length (sieve n)

{-# COMPILE AGDA2LAMBOX countPrimes #-}
