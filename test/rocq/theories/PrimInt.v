From Stdlib Require Import PrimInt63 Uint63 List.
Import ListNotations.
Open Scope uint63_scope.

(* Every PrimInt63 operation, with the edge cases of division by zero, shifts
   past 63 bits, carries and the three comparisons.  The booleans of eqb, ltb
   and leb are observed through b2n, so a backend that encodes bool with the
   wrong constructor order gives wrong numbers. *)
Definition b2n (b : bool) : nat := if b then 1%nat else 0%nat.
Definition c2n (c : comparison) : nat := match c with Eq => 0%nat | Lt => 1%nat | Gt => 2%nat end.
Fixpoint n_of (fuel : nat) (i : int) : nat :=
  match fuel with
  | O => 0%nat
  | S f => if PrimInt63.eqb i 0 then 0%nat else S (n_of f (PrimInt63.sub i 1))
  end.
Definition to_nat := n_of 200%nat.
Definition car (c : carry int) : nat * nat :=
  match c with C0 x => (0%nat, to_nat x) | C1 x => (1%nat, to_nat x) end.

Definition max_int := 9223372036854775807%uint63. (* 2^63 - 1 *)

Definition test : list nat :=
  [ to_nat (PrimInt63.add 3 4)               (* 7 *)
  ; to_nat (PrimInt63.sub 10 3)              (* 7 *)
  ; to_nat (PrimInt63.mul 6 7)               (* 42 *)
  ; to_nat (PrimInt63.div 7 0)               (* 0 *)
  ; to_nat (PrimInt63.mod 7 0)               (* 7 *)
  ; to_nat (PrimInt63.lsl 1 63)              (* 0 *)
  ; to_nat (PrimInt63.lsr 64 70)             (* 0 *)
  ; to_nat (PrimInt63.lsl 1 5)               (* 32 *)
  ; to_nat (PrimInt63.land 12 10)            (* 8 *)
  ; to_nat (PrimInt63.lor 12 10)             (* 14 *)
  ; to_nat (PrimInt63.lxor 12 10)            (* 6 *)
  ; b2n (PrimInt63.eqb 5 5)                  (* 1 *)
  ; b2n (PrimInt63.eqb 5 6)                  (* 0 *)
  ; b2n (PrimInt63.ltb 5 6)                  (* 1 *)
  ; b2n (PrimInt63.leb 6 5)                  (* 0 *)
  ; c2n (PrimInt63.compare 5 5)              (* 0 *)
  ; c2n (PrimInt63.compare 5 6)              (* 1 *)
  ; c2n (PrimInt63.compare 6 5)              (* 2 *)
  ; fst (car (PrimInt63.addc max_int 2))     (* 1 *)
  ; snd (car (PrimInt63.addc max_int 2))     (* 1 *)
  ; fst (car (PrimInt63.addcarryc 2 3))      (* 0 *)
  ; snd (car (PrimInt63.addcarryc 2 3))      (* 6 *)
  ; fst (car (PrimInt63.subc 2 3))           (* 1 *)
  ; fst (car (PrimInt63.subcarryc 5 3))      (* 0 *)
  ; snd (car (PrimInt63.subcarryc 5 3))      (* 1 *)
  ; to_nat (fst (PrimInt63.mulc max_int 4))  (* 1 *)
  ; to_nat (PrimInt63.head0 1)               (* 62 *)
  ; to_nat (PrimInt63.tail0 8)               (* 3 *)
  ; to_nat (fst (PrimInt63.diveucl 17 5))    (* 3 *)
  ; to_nat (snd (PrimInt63.diveucl 17 5))    (* 2 *)
  ; to_nat (snd (PrimInt63.diveucl 17 0))    (* 17 *)
  ; to_nat (fst (PrimInt63.diveucl_21 0 17 5)) (* 3 *)
  ; to_nat (snd (PrimInt63.diveucl_21 0 17 5)) (* 2 *)
  ; to_nat (PrimInt63.addmuldiv 1 3 0)       (* 6 *)
  ].

Example test_value :
  test = [7;7;42;0;7;0;0;32;8;14;6;1;0;1;0;0;1;2;1;1;0;6;1;0;1;3;62;3;3;2;17;3;2;6]%nat.
Proof. vm_compute. reflexivity. Qed.
