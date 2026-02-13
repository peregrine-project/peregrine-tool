/-
  Tak (Takeuchi) Function Benchmark
  tak(x, y, z) = if x <= y then z
                 else tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y))
-/

partial def tak (x y z : Int) : Int :=
  if x <= y then z
  else tak (tak (x - 1) y z) (tak (y - 1) z x) (tak (z - 1) x y)

@[noinline] def runBenchmark (x y z : Int) : Int := tak x y z

def main (args : List String) : IO Unit := do
  let x := args.head?.bind String.toInt? |>.getD 18
  let y := (args.drop 1).head?.bind String.toInt? |>.getD 12
  let z := (args.drop 2).head?.bind String.toInt? |>.getD 6
  let start ← IO.monoNanosNow
  let result := runBenchmark x y z
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
