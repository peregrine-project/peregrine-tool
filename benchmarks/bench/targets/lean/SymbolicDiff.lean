/-
  Symbolic Differentiation Benchmark
  Differentiate algebraic expressions symbolically
-/

inductive Expr where
  | const : Int → Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | pow : Expr → Int → Expr
  | ln : Expr → Expr
  | exp : Expr → Expr
deriving Repr

def Expr.diff : Expr → Expr
  | .const _ => .const 0
  | .var => .const 1
  | .add e1 e2 => .add e1.diff e2.diff
  | .sub e1 e2 => .sub e1.diff e2.diff
  | .mul e1 e2 => .add (.mul e1.diff e2) (.mul e1 e2.diff)
  | .div e1 e2 => .div (.sub (.mul e1.diff e2) (.mul e1 e2.diff)) (.mul e2 e2)
  | .pow e n => .mul (.mul (.const n) (.pow e (n - 1))) e.diff
  | .ln e => .div e.diff e
  | .exp e => .mul (.exp e) e.diff

partial def Expr.simplify : Expr → Expr
  | .add (.const 0) e2 => e2.simplify
  | .add e1 (.const 0) => e1.simplify
  | .add (.const a) (.const b) => .const (a + b)
  | .sub e1 (.const 0) => e1.simplify
  | .sub (.const a) (.const b) => .const (a - b)
  | .mul (.const 0) _ => .const 0
  | .mul _ (.const 0) => .const 0
  | .mul (.const 1) e2 => e2.simplify
  | .mul e1 (.const 1) => e1.simplify
  | .mul (.const a) (.const b) => .const (a * b)
  | .div e1 (.const 1) => e1.simplify
  | .pow _ 0 => .const 1
  | .pow e 1 => e.simplify
  | .add e1 e2 => .add e1.simplify e2.simplify
  | .sub e1 e2 => .sub e1.simplify e2.simplify
  | .mul e1 e2 => .mul e1.simplify e2.simplify
  | .div e1 e2 => .div e1.simplify e2.simplify
  | .pow e1 n => .pow e1.simplify n
  | .ln e1 => .ln e1.simplify
  | .exp e1 => .exp e1.simplify
  | e => e

def diffSimplify (e : Expr) : Expr :=
  e.diff.simplify

def Expr.size : Expr → Nat
  | .const _ => 1
  | .var => 1
  | .add e1 e2 => 1 + e1.size + e2.size
  | .sub e1 e2 => 1 + e1.size + e2.size
  | .mul e1 e2 => 1 + e1.size + e2.size
  | .div e1 e2 => 1 + e1.size + e2.size
  | .pow e1 _ => 1 + e1.size
  | .ln e1 => 1 + e1.size
  | .exp e1 => 1 + e1.size

def nestedPoly : Nat → Expr
  | 0 => .var
  | n + 1 => .add (.mul (.const (Int.ofNat (n + 1))) (.pow .var (Int.ofNat (n + 1)))) (nestedPoly n)

def symbolicDiffBench (n : Nat) : Nat :=
  let poly := nestedPoly n
  let deriv := diffSimplify poly
  deriv.size

@[noinline] def runBenchmark (n : Nat) : Nat := symbolicDiffBench n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toNat? |>.getD 20
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
