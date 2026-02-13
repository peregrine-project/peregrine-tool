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
calcIterations maxDepth depth minDepth = pow2 (maxDepth - depth + minDepth)

runIterations : Nat → Nat → Nat → Nat
runIterations 0       _     acc = acc
runIterations (suc n) depth acc =
  runIterations n depth (acc + makeCheck depth)

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

binaryTreesSimple : Nat → Nat
binaryTreesSimple n =
  let minDepth  = 4
      maxDepth  = max (minDepth + 2) n
      stretch   = stretchTree maxDepth
      longTree  = treeMake maxDepth
      longCheck = treeCheck longTree
  in stretch + longCheck

binaryTreesBench : Nat → Nat
binaryTreesBench n = binaryTreesSimple n
