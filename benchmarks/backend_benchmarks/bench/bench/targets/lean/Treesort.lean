/-
  Treesort Benchmark
  Sorting by inserting into BST then flattening with in-order traversal
-/

inductive BST where
  | leaf : BST
  | node : BST → Nat → BST → BST
deriving Repr

def BST.insert (x : Nat) : BST → BST
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x < v then .node (l.insert x) v r
    else if v < x then .node l v (r.insert x)
    else .node l v r  -- duplicate

def buildTree (l : List Nat) : BST :=
  l.foldl (fun t x => t.insert x) .leaf

def BST.inorder : BST → List Nat
  | .leaf => []
  | .node l v r => l.inorder ++ [v] ++ r.inorder

def treesort (l : List Nat) : List Nat :=
  (buildTree l).inorder

def makeListAux (seed n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | n' + 1 =>
    let next := (seed * 1103515245 + 12345) % 2147483648
    makeListAux next n' (next :: acc)

def makeList (n : Nat) : List Nat :=
  makeListAux 42 n []

def isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x <= y && isSorted (y :: rest)

def treesortBench (n : Nat) : Nat :=
  let l := makeList n
  let sorted := treesort l
  if isSorted sorted then sorted.length else 0

@[noinline] def runBenchmark (n : Nat) : Nat := treesortBench n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 1000
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
