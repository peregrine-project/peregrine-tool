(** IO as a free monad, interpreted in Rocq by world passing.  Only the two
    primitive axioms are realized per backend; the interpreter is extracted
    with the program. *)
From Peregrine.Plugin Require Import Loader.
From Stdlib Require Import PrimInt63 Uint63.

Inductive op := PutInt (n : int) | GetInt.
Inductive resp := RUnit | RInt (n : int).

Inductive free (A : Type) : Type :=
| Pure (a : A)
| Op (o : op) (k : resp -> free A).
Arguments Pure {A} a.
Arguments Op {A} o k.

Fixpoint bind {A B} (m : free A) (f : A -> free B) : free B :=
  match m with
  | Pure a => f a
  | Op o k => Op o (fun r => bind (k r) f)
  end.

Definition put (n : int) : free unit := Op (PutInt n) (fun _ => Pure tt).
Definition get : free int :=
  Op GetInt (fun r => match r with RInt n => Pure n | RUnit => Pure 0%uint63 end).

(** The program: read x, print x and x + 1, return x + x. *)
Definition prog : free int :=
  bind get (fun x => bind (put x) (fun _ => bind (put (add x 1)) (fun _ => Pure (add x x)))).

(** The interpreter.  [world] is data, so each primitive call depends on the
    previous one and evaluation keeps their order. *)
Inductive world : Set := token.
Axiom put_int : int -> world -> world.
Axiom get_int : world -> int * world.

Fixpoint interp {A} (m : free A) (w : world) : A * world :=
  match m with
  | Pure a => (a, w)
  | Op (PutInt n) k => interp (k RUnit) (put_int n w)
  | Op GetInt k => let '(x, w') := get_int w in interp (k (RInt x)) w'
  end.

Definition main : int := fst (interp prog token).

Peregrine Extract "build/FreeIO.ast" main.
