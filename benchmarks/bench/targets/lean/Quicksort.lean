/-
  Quicksort Benchmark
  Functional quicksort using list partitioning
-/

def partition (pivot : Nat) (l : List Nat) : List Nat × List Nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let (lo, hi) := partition pivot xs
    if x < pivot then (x :: lo, hi) else (lo, x :: hi)

partial def quicksort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | [x] => [x]
  | pivot :: rest =>
    let (lo, hi) := partition pivot rest
    quicksort lo ++ [pivot] ++ quicksort hi

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

def quicksortBench (n : Nat) : Nat :=
  let l := makeList n
  let sorted := quicksort l
  if isSorted sorted then sorted.length else 0

@[noinline] def runBenchmark (n : Nat) : Nat := quicksortBench n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 1000
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
