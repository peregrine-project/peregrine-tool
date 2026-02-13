/-
  N-Queens Benchmark
  Classic backtracking: place N queens on NxN board with no attacks
-/

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

@[noinline] def runBenchmark (n : Nat) : Nat := nqueens n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 8
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
