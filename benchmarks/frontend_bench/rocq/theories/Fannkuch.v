(** * Fannkuch Redux Benchmark

    From the Computer Language Benchmarks Game.
    Indexed-access to tiny integer-sequence.

    https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/fannkuchredux.html

    The fannkuch benchmark computes the maximum number of "flips" (reversals
    of the prefix) needed to sort a permutation.
*)

From Stdlib Require Import List Arith.
Import ListNotations.

(* Lean implementation of tail recursive append *)
Fixpoint reverseAux {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | a::l => reverseAux l (a :: l2)
  end.
Definition reverse {A : Type} (l : list A) : list A :=
  reverseAux l [].
Definition appendTR {A : Type} (l1 l2 : list A) : list A :=
  reverseAux (reverse l1) l2.

(** Reverse the first n elements of a list *)
Fixpoint reversePrefixAux {A : Type} (n : nat) (l : list A) (acc : list A) : list A :=
  match n, l with
  | O, _ => appendTR acc l
  | S n', x :: xs => reversePrefixAux n' xs (x :: acc)
  | _, [] => acc
  end.

Definition reversePrefix {A : Type} (n : nat) (l : list A) : list A :=
  reversePrefixAux n l [].

(** One flip operation: reverse prefix of length = first element + 1 *)
Definition flip_ (perm : list nat) : list nat :=
  match perm with
  | [] => []
  | x :: _ => reversePrefix (S x) perm
  end.

(** Count flips until first element is 0 *)
#[bypass_check(guard)]
Fixpoint countFlipsAux (perm : list nat) (count : nat) {struct perm} : nat :=
  match perm with
  | [] => count
  | 0 :: _ => count  (* Sorted when first element is 0 *)
  | _ => countFlipsAux (flip_ perm) (S count)
  end.

Definition countFlips (perm : list nat) : nat :=
  countFlipsAux perm 0.

Fixpoint splitAt {A : Type} (n : nat) (l : list A) : list A * list A :=
  match n, l with
  | O, _ => ([], l)
  | S _, [] => ([], [])
  | S n', x :: xs =>
    let '(ys, zs) := splitAt n' xs in
    (x :: ys, zs)
  end.

Definition rotatePrefix {A : Type} (l : list A) (n : nat) : list A :=
  match l, n with
  | [], _ => []
  | l, 0 => l
  | l, 1 => l
  | x :: xs, S n =>
    let (prefix_rest, suffix) := splitAt n xs in
    appendTR prefix_rest (appendTR [x] suffix)
  end.

Fixpoint setAt {A : Type} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: xs, O => v :: xs
  | x :: xs, S n => x :: setAt xs n v
  end.

Fixpoint getAt (l : list nat) (i : nat) : nat :=
  match l, i with
  | [], _ => O
  | x :: _, O => x
  | _ :: xs, S n => getAt xs n
  end.

#[bypass_check(guard)]
Fixpoint findI (counts : list nat) (i : nat) (n : nat) {struct n} : option nat :=
  if n <=? i then None
  else if getAt counts i <? i then Some i
  else findI counts (S i) n.

Fixpoint resetCounts (counts : list nat) (i : nat) : list nat :=
  match counts, i with
  | [], _ => []
  | c :: cs, O => c :: cs
  | _ :: cs, S n => O :: resetCounts cs n
  end.

Definition nextPerm (perm counts : list nat) (n : nat) : option (list nat * list nat) :=
  match findI counts 1 n with
  | None => None
  | Some i =>
    let perm' := rotatePrefix perm (i + 1) in
    let counts' := setAt counts i (getAt counts i + 1) in
    let counts'' := resetCounts counts' i in
    Some (perm', counts'')
  end.

#[bypass_check(guard)]
Fixpoint fannkuchLoop (perm counts : list nat) (n maxFlips : nat) {struct n} : nat :=
  let flips := countFlips perm in
  let maxFlips' := max maxFlips flips in
  match nextPerm perm counts n with
  | None => maxFlips'
  | Some (perm', counts') => fannkuchLoop perm' counts' n maxFlips'
  end.

Fixpoint invrange (n : nat) : list nat :=
  match n with
  | O => []
  | S n => n :: invrange n
  end.

Definition range (n : nat) : list nat :=
  rev (invrange n).

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n => x :: replicate n x
  end.

Definition fannkuch (n : nat) : nat :=
  let perm := range n in
  let counts := replicate n 0 in
  fannkuchLoop perm counts n 0.

From Peregrine.Plugin Require Import Loader.

Peregrine Extract "ast/Fannkuch.ast" fannkuch.
Peregrine Extract Typed "ast/Fannkuch_typed.ast" fannkuch.
