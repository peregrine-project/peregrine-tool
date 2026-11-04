(** The program of [FreeIO.v], on [nat], for a host-driven interpreter: the extracted
    value is the free-monad tree itself, and the host performs each operation
    and calls the continuation (see [host.mjs]).  The Wasm module has no
    imports. *)
From Peregrine.Plugin Require Import Loader.
Inductive op := PutNat (n : nat) | GetNat.
Inductive resp := RUnit | RNat (n : nat).

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

Definition put (n : nat) : free unit := Op (PutNat n) (fun _ => Pure tt).
Definition get : free nat :=
  Op GetNat (fun r => match r with RNat n => Pure n | RUnit => Pure 0 end).

(** Read x, print x and x + 1, return x + x. *)
Definition main : free nat :=
  bind get (fun x => bind (put x) (fun _ => bind (put (S x)) (fun _ => Pure (x + x)))).

Peregrine Extract "../build/WasmIO.ast" main.
