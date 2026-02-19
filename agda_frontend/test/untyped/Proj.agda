data Bool : Set where false true : Bool

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open Pair

pair : Pair Bool Bool
pair = true , false

second : Bool
second = snd pair
{-# COMPILE AGDA2LAMBOX second #-}
