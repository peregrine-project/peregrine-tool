/-
  Ackermann Function Benchmark
  A(0, n) = n + 1
  A(m, 0) = A(m-1, 1)
  A(m, n) = A(m-1, A(m, n-1))
-/

partial def ackermann (m n : Nat) : Nat :=
  match m with
  | 0 => n + 1
  | m' + 1 =>
    match n with
    | 0 => ackermann m' 1
    | n' + 1 => ackermann m' (ackermann m n')

@[noinline] def runBenchmark (m n : Nat) : Nat := ackermann m n

def main (args : List String) : IO Unit := do
  let m := args.head?.bind String.toNat? |>.getD 3
  let n := (args.drop 1).head?.bind String.toNat? |>.getD 10
  let start ← IO.monoNanosNow
  let result := runBenchmark m n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
