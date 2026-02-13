/-
  Sieve of Eratosthenes Benchmark
  Find all prime numbers up to a given limit
-/

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

def sumPrimes (n : Nat) : Nat :=
  (sieve n).foldl (· + ·) 0

@[noinline] def runBenchmark (n : Nat) : Nat := countPrimes n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 10000
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
