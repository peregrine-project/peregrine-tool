/-
  Lambda Calculus Interpreter Benchmark
  Untyped lambda calculus with de Bruijn indices
-/

inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | lit : Int → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | ifz : Term → Term → Term → Term
deriving Repr

inductive Value where
  | vInt : Int → Value
  | vClosure : List Value → Term → Value
deriving Repr

def lookup (n : Nat) (env : List Value) : Option Value :=
  (env.drop n).head?

partial def eval (env : List Value) (t : Term) : Option Value :=
  match t with
  | .var n => lookup n env
  | .lam body => some (.vClosure env body)
  | .app f arg =>
    match eval env f with
    | some (.vClosure env' body) =>
      match eval env arg with
      | some v => eval (v :: env') body
      | none => none
    | _ => none
  | .lit n => some (.vInt n)
  | .add e1 e2 =>
    match eval env e1, eval env e2 with
    | some (.vInt n1), some (.vInt n2) => some (.vInt (n1 + n2))
    | _, _ => none
  | .mul e1 e2 =>
    match eval env e1, eval env e2 with
    | some (.vInt n1), some (.vInt n2) => some (.vInt (n1 * n2))
    | _, _ => none
  | .ifz cond then_ else_ =>
    match eval env cond with
    | some (.vInt 0) => eval env then_
    | some (.vInt _) => eval env else_
    | _ => none

def toInt : Option Value → Int
  | some (.vInt n) => n
  | _ => 0

-- Factorial using explicit recursion pattern
def makeFactAux : Nat → Term
  | 0 => .lit 1
  | n + 1 =>
    .lam (.ifz (.var 0)
              (.lit 1)
              (.mul (.var 0) (.app (makeFactAux n) (.add (.var 0) (.lit (-1))))))

def factorialTerm : Term := makeFactAux 20

def lambdaInterpBench (n : Int) : Int :=
  toInt (eval [] (.app factorialTerm (.lit n)))

-- Church numerals
def churchZero : Term := .lam (.lam (.var 0))
def churchSucc : Term :=
  .lam (.lam (.lam (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0)))))

def churchNum : Nat → Term
  | 0 => churchZero
  | n + 1 => .app churchSucc (churchNum n)

def churchToInt : Term :=
  .lam (.app (.app (.var 0) (.lam (.add (.var 0) (.lit 1)))) (.lit 0))

def churchAdd : Term :=
  .lam (.lam (.lam (.lam (.app (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0))))))

def churchBench (n : Nat) : Int :=
  let cn := churchNum n
  let addNN := .app (.app churchAdd cn) cn
  toInt (eval [] (.app churchToInt addNN))

@[noinline] def runBenchmark (n : Int) : Int := lambdaInterpBench n

def main (args : List String) : IO Unit := do
  let n := args.head?.bind String.toInt? |>.getD 10
  let start ← IO.monoNanosNow
  let result := runBenchmark n
  if result == 0 then IO.println "zero" else pure ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"Result: {result}"
  IO.println s!"Time: {(elapsed - start).toFloat / 1000000.0} ms"
