/-
  N-Queens Benchmark - Extraction for Peregrine
  Classic backtracking: place N queens on NxN board with no attacks
-/
import LeanToLambdaBox

def attacks (c r c' : Nat) : Bool :=
  let diff := if c' < c then c - c' else c' - c
  c == c' || diff == r

def safeAux (placed : List Nat) (r c : Nat) : Bool :=
  match placed with
  | [] => true
  | c' :: rest =>
    if attacks c r c' then false
    else safeAux rest (r - 1) c

def safe (placed : List Nat) (c : Nat) : Bool :=
  safeAux placed placed.length c

partial def solveAux (n row : Nat) (placed : List Nat) : List (List Nat) :=
  if row == n then
    [placed]
  else
    let candidates := (List.range n).filter (fun c => safe placed c)
    candidates.flatMap (fun c => solveAux n (row + 1) (placed ++ [c]))

def solve (n : Nat) : List (List Nat) :=
  solveAux n 0 []

def nqueens (n : Nat) : Nat :=
  (solve n).length

-- Benchmark instances
def nqueens_8 : Nat := nqueens 8
def nqueens_10 : Nat := nqueens 10
def nqueens_11 : Nat := nqueens 11

-- Extract to LambdaBox AST
#erase nqueens_8 to "extracted/nqueens_8.ast"
#erase nqueens_10 to "extracted/nqueens_10.ast"
#erase nqueens_11 to "extracted/nqueens_11.ast"
