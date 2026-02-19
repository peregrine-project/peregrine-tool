(** * Sieve of Eratosthenes Benchmark

    Classic algorithm to find all prime numbers up to a given limit.
    Uses a purely functional approach with list filtering.

    Uses nat for simplicity.
*)

From Stdlib Require Import List Arith Bool.
Import ListNotations.

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
    List.rev (range_from_aux start (limit - start) [])
  else [].

(** Remove all multiples of p from the list *)
Definition remove_multiples (p : nat) (l : list nat) : list nat :=
  filter (fun n => negb (Nat.eqb (Nat.modulo n p) 0) || Nat.eqb n p) l.

(** Sieve of Eratosthenes with fuel *)
Fixpoint sieve_aux (fuel : nat) (candidates : list nat) (primes : list nat) : list nat :=
  match fuel with
  | O => primes ++ candidates
  | S fuel' =>
      match candidates with
      | [] => primes
      | p :: rest =>
          sieve_aux fuel' (remove_multiples p rest) (primes ++ [p])
      end
  end.

Definition sieve (n : nat) : list nat :=
  sieve_aux n (range_from 2 n) [].

(** Count primes up to n *)
Definition count_primes (n : nat) : nat :=
  length (sieve n).

(** Sum of primes up to n *)
Definition sum_primes (n : nat) : nat :=
  fold_left Nat.add (sieve n) 0.

(** Test: primes up to 30 *)
Definition test_sieve_30 : list nat := sieve 30.
(* Should be [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] *)

(** Test: count primes up to 100 *)
Definition test_count_100 : nat := count_primes 100.
(* Should be 25 *)

(** Benchmark: count primes up to 10000 *)
Definition sieve_bench : nat := count_primes 10000.
(* Should be 1229 *)

(** Benchmark: sum of primes up to 2000 *)
Definition sum_primes_bench : nat := sum_primes 2000.
