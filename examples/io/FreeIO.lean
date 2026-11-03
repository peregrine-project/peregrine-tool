import LeanToLambdaBox

/-! Lean IO as a free monad: a program written against `MonadNatIO` runs natively in `IO`
and, instantiated at `Free`, is a pure tree that the erasers translate like other data.
The operations carry naturals only, because string literals are not yet erased. -/

namespace FreeIO

inductive Op where
  | putNat (n : Nat)
  | getNat

def Op.Res : Op → Type
  | .putNat _ => Unit
  | .getNat => Nat

inductive Free (α : Type) where
  | pure (a : α)
  | op (o : Op) (k : o.Res → Free α)

def Free.bind {α β} : Free α → (α → Free β) → Free β
  | .pure a, f => f a
  | .op o k, f => .op o (fun r => (k r).bind f)

instance : Monad Free where
  pure := .pure
  bind := Free.bind

class MonadNatIO (m : Type → Type) where
  putNat : Nat → m Unit
  getNat : m Nat

instance : MonadNatIO IO where
  putNat n := IO.println (toString n)
  getNat := do
    let s ← (← IO.getStdin).getLine
    return s.toList.foldl (fun n c => if c.isDigit then n * 10 + (c.toNat - 48) else n) 0

instance : MonadNatIO Free where
  putNat n := .op (.putNat n) .pure
  getNat := .op .getNat .pure

open MonadNatIO in
def prog {m} [Monad m] [MonadNatIO m] : m Nat := do
  let x ← getNat
  putNat x
  putNat (x + 1)
  return x + x

/-- A pure interpreter: feeds `inputs` to `getNat` and records what `putNat` prints. -/
def run {α} : Free α → List Nat → List Nat × Option α
  | .pure a, _ => ([], some a)
  | .op (.putNat n) k, ins => let (out, r) := run (k ()) ins; (n :: out, r)
  | .op .getNat k, i :: ins => run (k i) ins
  | .op .getNat _, [] => ([], none)

def eqN : Nat → Nat → Bool
  | .zero, .zero => true
  | .succ a, .succ b => eqN a b
  | _, _ => false

def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: m => eqN a b && eqL l m
  | _, _ => false

/-- `prog` with input 3 prints 3 and 4 and returns 6. -/
def c : Bool :=
  match run (prog (m := Free)) [3] with
  | (out, some r) => eqL out [3, 4] && eqN r 6
  | (_, none) => false

#eval c
#eval run (prog (m := Free)) [3]

/-! The effectful interpreter, by world passing. Only the two primitives are realized
per backend; `World` is data, so each primitive call depends on the previous one. -/

inductive World where
  | token
  deriving Inhabited

@[extern "freeio_put_nat"] opaque primPutNat : Nat → World → World
@[extern "freeio_get_nat"] opaque primGetNat : World → Nat × World

def interp {α} : Free α → World → α × World
  | .pure a, w => (a, w)
  | .op (.putNat n) k, w => interp (k ()) (primPutNat n w)
  | .op .getNat k, w => let r := primGetNat w; interp (k r.1) r.2

def ioMain : Nat := (interp (prog (m := Free)) .token).1

end FreeIO
