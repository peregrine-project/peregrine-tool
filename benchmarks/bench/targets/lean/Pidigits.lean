/-
  Pidigits Benchmark
  From the Computer Language Benchmarks Game
  Streaming arbitrary-precision arithmetic
  Uses the unbounded spigot algorithm
-/

-- Linear fractional transformation (matrix)
structure LFT where
  q : Int
  r : Int
  s : Int
  t : Int
deriving Repr

def LFT.compose (a b : LFT) : LFT :=
  LFT.mk
    (a.q * b.q + a.r * b.s)
    (a.q * b.r + a.r * b.t)
    (a.s * b.q + a.t * b.s)
    (a.s * b.r + a.t * b.t)

def LFT.extract (lft : LFT) (x : Int) : Int :=
  (lft.q * x + lft.r) / (lft.s * x + lft.t)

def LFT.init : LFT := LFT.mk 1 0 0 1

def lftn (k : Nat) : LFT :=
  let k' : Int := k
  LFT.mk k' (4 * k' + 2) 0 (2 * k' + 1)

def LFT.safe (lft : LFT) (n : Int) : Bool :=
  n == lft.extract 4

def LFT.prod (lft : LFT) (n : Int) : LFT :=
  (LFT.mk 10 (-10 * n) 0 1).compose lft

-- Generate n digits of pi, return them as a number
partial def pidigitsLoop (z : LFT) (k : Nat) (remaining : Nat) (acc : Int) : Int :=
  if remaining == 0 then acc
  else
    let y := z.extract 3
    if z.safe y then
      pidigitsLoop (z.prod y) k (remaining - 1) (acc * 10 + y)
    else
      let z' := z.compose (lftn k)
      pidigitsLoop z' (k + 1) remaining acc

def pidigitsNumber (n : Nat) : Int :=
  pidigitsLoop LFT.init 1 n 0

@[noinline] def runBenchmark (n : Nat) : Int := pidigitsNumber n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 27
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
