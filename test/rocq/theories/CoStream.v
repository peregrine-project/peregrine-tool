From Stdlib Require Import List.
Import ListNotations.

CoInductive stream := Cons : nat -> stream -> stream.

CoFixpoint from (n : nat) : stream := Cons n (from (S n)).

CoFixpoint ev : stream := Cons 0 od
with od : stream := Cons 1 ev.

Fixpoint take (k : nat) (s : stream) : list nat :=
  match k with
  | 0 => []
  | S k' => match s with Cons x s' => x :: take k' s' end
  end.

Definition test : list nat := take 2 (from 0) ++ take 2 ev.
