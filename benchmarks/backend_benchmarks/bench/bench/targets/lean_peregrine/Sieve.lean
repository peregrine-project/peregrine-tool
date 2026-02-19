/-
  Sieve of Eratosthenes Benchmark - Extraction for Peregrine
  Find all prime numbers up to a given limit
-/
import LeanToLambdaBox

def removeMultiples (p : Nat) (l : List Nat) : List Nat :=
  l.filter (fun n => n % p != 0 || n == p)

partial def sieveAux (candidates primes : List Nat) : List Nat :=
  match candidates with
  | [] => primes
  | p :: rest => sieveAux (removeMultiples p rest) (primes ++ [p])

def sieve (n : Nat) : List Nat :=
  if n < 2 then []
  else sieveAux (List.range (n - 1) |>.map (· + 2)) []

def countPrimes (n : Nat) : Nat :=
  (sieve n).length

-- Benchmark instances
def sieve_1000 : Nat := countPrimes 1000
def sieve_5000 : Nat := countPrimes 5000
def sieve_10000 : Nat := countPrimes 10000

-- Extract to LambdaBox AST
#erase sieve_1000 to "extracted/sieve_1000.ast"
#erase sieve_5000 to "extracted/sieve_5000.ast"
#erase sieve_10000 to "extracted/sieve_10000.ast"
