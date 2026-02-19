/-
  Sieve of Eratosthenes Benchmark - Extraction for Peregrine
  Find all prime numbers up to a given limit
-/
import LeanToLambdaBox

def rangeFromAux (start n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | n' + 1 =>
    if start <= (n' + start) then
      rangeFromAux start n' ((n' + start) :: acc)
    else acc

def rangeFrom (start limit : Nat) : List Nat :=
  if start <= limit then
    rangeFromAux start (limit - start) []
  else []

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

def removeMultiples (p : Nat) (l : List Nat) : List Nat :=
  l.filter (fun n => modulo n p != 0 || n == p)

def sieveAux (fuel : Nat) (candidates primes : List Nat) : List Nat :=
  match fuel with
  | 0 => primes ++ candidates
  | fuel' + 1 =>
    match candidates with
    | [] => primes
    | p :: rest => sieveAux fuel' (removeMultiples p rest) (primes ++ [p])

def sieve (n : Nat) : List Nat :=
  sieveAux n (rangeFrom 2 (n + 1)) []

def countPrimes (n : Nat) : Nat :=
  (sieve n).length

-- Extract to LambdaBox AST
#erase countPrimes config {extern := .preferLogical, nat := .peano,} to "ast/Sieve.ast"
