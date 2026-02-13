/-
  Quicksort Benchmark - Extraction for Peregrine
  Functional quicksort using list partitioning
-/
import LeanToLambdaBox

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

-- Benchmark instances
def quicksort_100 : Nat := quicksortBench 100
def quicksort_500 : Nat := quicksortBench 500
def quicksort_1000 : Nat := quicksortBench 1000

-- Extract to LambdaBox AST
#erase quicksort_100 to "extracted/quicksort_100.ast"
#erase quicksort_500 to "extracted/quicksort_500.ast"
#erase quicksort_1000 to "extracted/quicksort_1000.ast"
