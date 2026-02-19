{-# OPTIONS --erasure #-}
{-
  Binary Trees Benchmark
  From the Computer Language Benchmarks Game
  Allocate and deallocate many binary trees
-}

module BinaryTrees where

open import Prelude

data Tree : Set where
  leaf : Tree
  node : Tree → Nat → Tree → Tree

treeMake : Nat → Tree
treeMake 0       = leaf
treeMake (suc n) = node (treeMake n) 0 (treeMake n)

treeCheck : Tree → Nat
treeCheck leaf         = 0
treeCheck (node l _ r) = 1 + treeCheck l + treeCheck r

makeCheck : Nat → Nat
makeCheck d = treeCheck (treeMake d)

stretchTree : Nat → Nat
stretchTree maxDepth = makeCheck (suc maxDepth)

calcIterations : Nat → Nat → Nat → Nat
calcIterations maxDepth depth minDepth = pow2 ((maxDepth - depth) + minDepth)


runIterations : Nat → Nat → Nat → Nat
runIterations 0       _     acc = acc
runIterations (suc n) depth acc =
  runIterations n depth (makeCheck depth + acc)

runDepthsAux : Nat → Nat → Nat → Nat → List Nat → List Nat
runDepthsAux zero _ _ _ acc = acc
runDepthsAux (suc fuel) minDepth currentDepth maxDepth acc
  with currentDepth < maxDepth
... | true =
      let iterations = calcIterations maxDepth currentDepth minDepth
          result     = runIterations iterations currentDepth 0
      in runDepthsAux fuel minDepth (2 + currentDepth) maxDepth (result ∷ acc)
... | false = acc

runDepths : Nat → Nat → List Nat
runDepths minDepth maxDepth =
  runDepthsAux (suc maxDepth) minDepth minDepth maxDepth []

sumDepths : List Nat -> Nat
sumDepths [] = 0
sumDepths (x ∷ xs) = x + sumDepths xs

binaryTreesMain : Nat -> (Nat × (List Nat × Nat))
binaryTreesMain n =
  let minDepth     = 4
      maxDepth     = max (2 + minDepth) n
      stretch      = stretchTree maxDepth
      longTree     = treeMake maxDepth
      depthResults = runDepths minDepth maxDepth
      longCheck    = treeCheck longTree
  in (stretch , (depthResults , longCheck))

binaryTreesSimpleAux : Nat × (List Nat × Nat) → Nat
binaryTreesSimpleAux (stretch , (depths , longCheck)) = stretch + longCheck + sumDepths depths

binaryTreesSimple : Nat → Nat
binaryTreesSimple n = binaryTreesSimpleAux (binaryTreesMain n)

binaryTreesBench : Nat → Nat
binaryTreesBench n = binaryTreesSimple n

{-# COMPILE AGDA2LAMBOX binaryTreesBench #-}
