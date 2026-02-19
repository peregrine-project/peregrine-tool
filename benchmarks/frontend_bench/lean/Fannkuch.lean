/-
  Fannkuch Redux Benchmark
  From the Computer Language Benchmarks Game
  Indexed-access to tiny integer-sequence

  Purely functional implementation using immutable lists
-/
import LeanToLambdaBox

-- Reverse the first n elements of a list, keeping the rest
def reversePrefixAux {α : Type} (n : Nat) (l : List α) (acc : List α) : List α :=
  match n, l with
  | 0, _ => acc ++ l
  | n' + 1, x :: xs => reversePrefixAux n' xs (x :: acc)
  | _, [] => acc

def reversePrefix {α : Type} (n : Nat) (l : List α) : List α :=
  reversePrefixAux n l []

-- One flip_ operation: reverse prefix of length = first element + 1
def flip_ (perm : List Nat) : List Nat :=
  match perm with
  | [] => []
  | x :: _ => reversePrefix (x + 1) perm

-- Count flips until first element is 0
partial def countFlipsAux (perm : List Nat) (count : Nat) : Nat :=
  match perm with
  | [] => count
  | 0 :: _ => count
  | _ => countFlipsAux (flip_ perm) (count + 1)

def countFlips (perm : List Nat) : Nat :=
  countFlipsAux perm 0

-- Rotate first n elements: [a, b, c, d, ...] -> [b, c, d, a, ...]
def rotatePrefix (l : List Nat) (n : Nat) : List Nat :=
  match l, n with
  | [], _ => []
  | l, 0 => l
  | l, 1 => l
  | x :: xs, n + 1 =>
    let (prefix_rest, suffix) := xs.splitAt n
    prefix_rest ++ [x] ++ suffix

-- Update element at position i in a list
def setAt {α : Type} (l : List α) (i : Nat) (v : α) : List α :=
  match l, i with
  | [], _ => []
  | _ :: xs, 0 => v :: xs
  | x :: xs, n + 1 => x :: setAt xs n v

-- Get element at position i in a list
def getAt (l : List Nat) (i : Nat) : Nat :=
  match l, i with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => getAt xs n

-- Find the index i where count[i] < i, starting from index 1
def findI (counts : List Nat) (i : Nat) (n : Nat) : Option Nat :=
  if i >= n then none
  else if getAt counts i < i then some i
  else findI counts (i + 1) n

-- Reset counts from 0 to i-1 to 0
def resetCounts (counts : List Nat) (i : Nat) : List Nat :=
  match counts, i with
  | [], _ => []
  | c :: cs, 0 => c :: cs
  | _ :: cs, n + 1 => 0 :: resetCounts cs n

-- Generate next permutation using Heap's algorithm variant
partial def nextPerm (perm counts : List Nat) (n : Nat) : Option (List Nat × List Nat) :=
  match findI counts 1 n with
  | none => none
  | some i =>
    let perm' := rotatePrefix perm (i + 1)
    let counts' := setAt counts i (getAt counts i + 1)
    let counts'' := resetCounts counts' i
    some (perm', counts'')

-- Main loop: iterate through all permutations tracking max flips
partial def fannkuchLoop (perm counts : List Nat) (n maxFlips : Nat) : Nat :=
  let flips := countFlips perm
  let maxFlips' := max maxFlips flips
  match nextPerm perm counts n with
  | none => maxFlips'
  | some (perm', counts') => fannkuchLoop perm' counts' n maxFlips'

def fannkuch (n : Nat) : Nat :=
  let perm := List.range n
  let counts := List.replicate n 0
  fannkuchLoop perm counts n 0

@[noinline] def runBenchmark (n : Nat) : Nat := fannkuch n


-- Extract to LambdaBox AST
#erase runBenchmark config {extern := .preferLogical, nat := .peano,} to "ast/Fannkuch.ast"
