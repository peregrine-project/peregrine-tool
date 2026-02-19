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

def quicksort_fuel (fuel : Nat) (l : List Nat) : List Nat :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    match l with
    | [] => []
    | [x] => [x]
    | pivot :: rest =>
      let (lo, hi) := partition pivot rest
      quicksort_fuel fuel' lo ++ [pivot] ++ quicksort_fuel fuel' hi

def quicksort (l : List Nat) : List Nat :=
  quicksort_fuel (l.length * l.length) l

def divmod (x y u : Nat) : Nat :=
  match x with
  | 0 => u
  | x' + 1 =>
    match u with
    | 0 => divmod x' y y
    | u' + 1 => divmod x' y u'

def modulo (x y : Nat) : Nat :=
  match y with
  | 0 => x
  | y' + 1 => y' - (divmod x y' y')

def makeListAux (seed n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | n' + 1 =>
    let next := modulo ((seed * 49) + 12) 214
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


-- Extract to LambdaBox AST
#erase quicksortBench config {extern := .preferLogical, nat := .peano,} to "ast/Quicksort.ast"
