/-
  Binary Trees Benchmark - Extraction for Peregrine
  From the Computer Language Benchmarks Game
  Allocate and deallocate many binary trees
-/
import LeanToLambdaBox

inductive Tree where
  | leaf : Tree
  | node : Tree → Int → Tree → Tree

def Tree.make (depth : Nat) : Tree :=
  match depth with
  | 0 => .leaf
  | n + 1 => .node (make n) 0 (make n)

def Tree.check : Tree → Int
  | .leaf => 0
  | .node l _ r => 1 + l.check + r.check

def makeCheck (depth : Nat) : Int :=
  (Tree.make depth).check

def stretchTree (maxDepth : Nat) : Int :=
  makeCheck (maxDepth + 1)

def calcIterations (maxDepth depth minDepth : Nat) : Nat :=
  2 ^ (maxDepth - depth + minDepth)

def runIterations (iterations depth : Nat) (acc : Int) : Int :=
  match iterations with
  | 0 => acc
  | n + 1 => runIterations n depth (acc + makeCheck depth)

partial def runDepthsAux (minDepth currentDepth maxDepth : Nat) (acc : List Int) : List Int :=
  if currentDepth > maxDepth then acc
  else
    let iterations := calcIterations maxDepth currentDepth minDepth
    let result := runIterations iterations currentDepth 0
    runDepthsAux minDepth (currentDepth + 2) maxDepth (acc ++ [result])

def runDepths (minDepth maxDepth : Nat) : List Int :=
  runDepthsAux minDepth minDepth maxDepth []

def binaryTreesMain (n : Nat) : Int × List Int × Int :=
  let minDepth := 4
  let maxDepth := max (minDepth + 2) n
  let stretch := stretchTree maxDepth
  let longTree := Tree.make maxDepth
  let depthResults := runDepths minDepth maxDepth
  let longCheck := longTree.check
  (stretch, depthResults, longCheck)

def binaryTreesSimple (n : Nat) : Int :=
  let (stretch, _, longCheck) := binaryTreesMain n
  stretch + longCheck

-- Benchmark instances
def binary_trees_10 : Int := binaryTreesSimple 10
def binary_trees_14 : Int := binaryTreesSimple 14

-- Extract to LambdaBox AST
#erase binary_trees_10 to "extracted/binary_trees_10.ast"
#erase binary_trees_14 to "extracted/binary_trees_14.ast"
