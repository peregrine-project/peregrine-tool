(** * Sieve of Eratosthenes Benchmark

    Classic algorithm to find all prime numbers up to a given limit.
    Uses a purely functional approach with list filtering.

    Uses nat for simplicity.
*)

From Stdlib Require Import List Arith Bool.
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

(** Generate list [2, 3, ..., n] *)
Fixpoint range_from_aux (start n : nat) (acc : list nat) : list nat :=
  match n with
  | O => acc
  | S n' =>
      if Nat.leb start (start + n') then
        range_from_aux start n' ((start + n') :: acc)
      else acc
  end.

Definition range_from (start limit : nat) : list nat :=
  if Nat.leb start limit then
    range_from_aux start (limit - start) []
  else [].

Fixpoint divmod (x y u : nat) : nat :=
  match x with
  | O => u
  | S x' =>
    match u with
    | O => divmod x' y y
    | S u' => divmod x' y u'
    end
  end.

Definition modulo (x y : nat) : nat :=
  match y with
  | O => x
  | S y' => y' - (divmod x y' y')
  end.

(** Remove all multiples of p from the list *)
Definition remove_multiples (p : nat) (l : list nat) : list nat :=
  filter (fun n =>
    (* if negb (Nat.eqb (Nat.modulo n p) 0) then true else Nat.eqb n p) l. *)
    if negb (Nat.eqb (modulo n p) 0) then true else Nat.eqb n p) l.

(** Sieve of Eratosthenes with fuel *)
Fixpoint sieve_aux (fuel : nat) (candidates : list nat) (primes : list nat) : list nat :=
  match fuel with
  | O => appendTR primes candidates
  | S fuel' =>
      match candidates with
      | [] => primes
      | p :: rest =>
          sieve_aux fuel' (remove_multiples p rest) (appendTR primes [p])
      end
  end.

Definition sieve (n : nat) : list nat :=
  sieve_aux n (range_from 2 (S n)) [].

(** Count primes up to n *)
Definition count_primes (n : nat) : nat :=
  length (sieve n).


From Peregrine.Plugin Require Import Loader.

Peregrine Extract "ast/Sieve.ast" count_primes.
Peregrine Extract Typed "ast/Sieve_typed.ast" count_primes.
