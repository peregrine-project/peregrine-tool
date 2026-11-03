(** Tasks: a computation started with [spawn] runs alongside the rest of the
    program, and [get] waits for its result.  [spawn] and [get] are axioms,
    realized per backend: with OCaml threads (concurrent, not parallel, on
    OCaml 4) and with Lean's [Task] (parallel, on Lean's thread pool).  Their
    meaning is [get (spawn f) = f tt]. *)
From Peregrine.Plugin Require Import Loader.

Axiom task : Type -> Type.
Axiom spawn : forall {A : Type}, (unit -> A) -> task A.
Axiom get : forall {A : Type}, task A -> A.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => match m with 0 => 1 | S k => fib m + fib k end
  end.

(** fib 20 + fib 21 = 6765 + 10946, computed by two tasks. *)
Definition main : nat :=
  let t1 := spawn (fun _ => fib 20) in
  let t2 := spawn (fun _ => fib 21) in
  get t1 + get t2.

Peregrine Extract "build/Tasks.ast" main.
