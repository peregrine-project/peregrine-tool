/-
  Binary Trees Benchmark
  From the Computer Language Benchmarks Game
  Allocate and deallocate many binary trees
-/

inductive Tree where
  | leaf : Tree
  | node : Tree → Int → Tree → Tree
deriving Repr

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

@[noinline] def runBenchmark (n : Nat) : Int := binaryTreesSimple n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 10
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  -- Force evaluation by checking the result
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
