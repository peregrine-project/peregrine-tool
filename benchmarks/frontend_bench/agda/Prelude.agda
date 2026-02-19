module Prelude where

open import Agda.Builtin.Bool     public
open import Agda.Builtin.Equality public
open import Agda.Builtin.List     public
open import Agda.Builtin.Maybe    public
open import Agda.Builtin.Nat      public
open import Agda.Builtin.String   public
open import Agda.Builtin.Unit     public
open import Agda.Primitive        public

variable
  a b : Level
  A   : Set a
  B   : Set b

infix -1 if_then_else_
if_then_else_ : Bool → A → A → A
if true  then x else y = x
if false then x else y = y

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

pow2 : Nat → Nat
pow2 0       = 1
pow2 (suc n) = double (pow2 n)

max : Nat → Nat → Nat
max x y = if x < y then y else x

infixr 6 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

pattern [_] x = _∷_ x []

foldr : (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

rev : List A → List A
rev = foldl (λ xs x → x ∷ xs) []

length : List A → Nat
length = foldr (λ _ → suc) 0

infixl 4 _,_
record _×_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

divmod : Nat → Nat → Nat → Nat
divmod 0 _ u = u
divmod (suc x') y 0 = divmod x' y y
divmod (suc x') y (suc u') = divmod x' y u'

-- mod n m ≡ n % m
mod : Nat → Nat → Nat
mod n 0 = n
mod n (suc m) = m - (divmod n m m)

splitAt : Nat → List A → (List A × List A)
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

setAt : List A → Nat → A → List A
setAt [] k y = []
setAt (x ∷ xs) zero    y = y ∷ xs
setAt (x ∷ xs) (suc k) y = x ∷ setAt xs k y

getAt : List Nat → Nat → Nat
getAt [] k = 0
getAt (x ∷ xs) zero = x
getAt (x ∷ xs) (suc k) = getAt xs k

updateAt : (A → A) → List A → Nat → List A
updateAt f [] k = []
updateAt f (x ∷ xs) zero    = f x ∷ xs
updateAt f (x ∷ xs) (suc k) = x   ∷ updateAt f xs k

findIndexAux : (P : Nat → A → Bool) → Nat → List A → Maybe Nat
findIndexAux P k []       = nothing
findIndexAux P k (x ∷ xs) =
  if P k x then just k
           else findIndexAux P (suc k) xs

-- find first index k such that P k xs[k] is true
findIndex : (P : Nat → A → Bool) → List A → Maybe Nat
findIndex {A = A} P = findIndexAux P 0

tail : List A → List A
tail [] = []
tail (_ ∷ xs) = xs

case_of_ : A → (A → B) → B
case x of f = f x

-- invrange n = [(n - 1) .. 0]
invrange range : Nat → List Nat
invrange 0       = []
invrange (suc n) = n ∷ invrange n

-- range n = [0 .. (n - 1)]
range n = rev (invrange n)

replicate : Nat → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

mapMaybe : (f : A → A) → Maybe A → Maybe A
mapMaybe f nothing = nothing
mapMaybe f (just x) = just (f x)


reverseAux : List A -> List A -> List A
reverseAux [] l = l
reverseAux (a ∷ l) l2 = reverseAux l (a ∷ l2)

reverse : List A -> List A
reverse l = reverseAux l []
appendTR : List A -> List A -> List A
appendTR l1 l2 = reverseAux (reverse l1) l2
