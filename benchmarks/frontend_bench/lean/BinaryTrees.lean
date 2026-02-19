/-
  Binary Trees Benchmark - Extraction for Peregrine
  From the Computer Language Benchmarks Game
  Allocate and deallocate many binary trees
-/
import LeanToLambdaBox

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

def Tree.make (depth : Nat) : Tree :=
  match depth with
  | 0 => .leaf
  | n + 1 => .node (make n) 0 (make n)

def Tree.check : Tree → Nat
  | .leaf => 0
  | .node l _ r => r.check + (l.check + 1)

def makeCheck (depth : Nat) : Nat :=
  (Tree.make depth).check

def stretchTree (maxDepth : Nat) : Nat :=
  makeCheck (maxDepth + 1)

def calcIterations (maxDepth depth minDepth : Nat) : Nat :=
  2 ^ (minDepth + (maxDepth - depth))

def runIterations (iterations depth : Nat) (acc : Nat) : Nat :=
  match iterations with
  | 0 => acc
  | n + 1 => runIterations n depth (acc + (makeCheck depth))

def runDepthsAux (fuel : Nat) (minDepth currentDepth maxDepth : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    if currentDepth < maxDepth then
      let iterations := calcIterations maxDepth currentDepth minDepth
      let result := runIterations iterations currentDepth 0
      runDepthsAux fuel' minDepth (currentDepth + 2) maxDepth (result :: acc)
    else
      acc

def runDepths (minDepth maxDepth : Nat) : List Nat :=
  runDepthsAux (maxDepth + 1) minDepth minDepth maxDepth []

def sumDepths (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => sumDepths xs + x

def binaryTreesMain (n : Nat) : Nat × List Nat × Nat :=
  let minDepth := 4
  let maxDepth := max (minDepth + 2) n
  let stretch := stretchTree maxDepth
  let longTree := Tree.make maxDepth
  let depthResults := runDepths minDepth maxDepth
  let longCheck := longTree.check
  (stretch, depthResults, longCheck)

def binaryTreesSimple (n : Nat) : Nat :=
  let (stretch, depths, longCheck) := binaryTreesMain n
  sumDepths depths + (longCheck + stretch)

-- Extract to LambdaBox AST
#erase binaryTreesSimple config {extern := .preferLogical, nat := .peano} to "ast/BinaryTrees.ast"
