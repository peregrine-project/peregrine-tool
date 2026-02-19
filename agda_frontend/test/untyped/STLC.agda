{-# OPTIONS --erasure #-}
open import Agda.Builtin.Nat

variable @0 n : Nat

data Type : Set where
  ℕ   : Type
  _⇒_ : Type → Type → Type

variable @0 α β : Type

infixl 7 _▷_
data Ctx : @0 Nat → Set where
  []  : Ctx zero
  _▷_ : Ctx n → Type → Ctx (suc n)

variable @0 Γ : Ctx n

infix 6 _∋_
data _∋_ : @0 Ctx n → @0 Type → Set where
  here  :          Γ ▷ α ∋ α
  there : Γ ∋ α → Γ ▷ β ∋ α

data _⊢_ (@0 Γ : Ctx n) : @0 Type → Set where
  var  : Γ ∋ α → Γ ⊢ α
  lam  : (Γ ▷ α) ⊢ β → Γ ⊢ (α ⇒ β)
  app  : Γ ⊢ (α ⇒ β) → Γ ⊢ α → Γ ⊢ β
  lit  : Nat → Γ ⊢ ℕ
  plus : Γ ⊢ ℕ → Γ ⊢ ℕ → Γ ⊢ ℕ

Value : Type → Set
Value ℕ       = Nat
Value (α ⇒ β) = Value α → Value β

data Env : @0 Ctx n → Set where
  []  : Env []
  _▷_ : Env Γ → Value α → Env (Γ ▷ α)

lookupEnv : Env Γ → Γ ∋ α → Value α
lookupEnv (env ▷ x) here = x
lookupEnv (env ▷ _) (there k) = lookupEnv env k

eval : Env Γ → Γ ⊢ α → Value α
eval env (var k)    = lookupEnv env k
eval env (lam u)    = λ x → eval (env ▷ x) u
eval env (app u v)  = eval env u (eval env v)
eval env (lit x)    = x
eval env (plus u v) = eval env u + eval env v

-- (λ x → x + 1) 1
test : Nat
test = eval [] (app (lam (plus (lit 1) (var here))) (lit 1)) 
{-# COMPILE AGDA2LAMBOX test #-}
