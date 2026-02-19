Require Import Arith List String.
Require Import VerifiedExtraction.Benchmarks.lib.vs.
Require Import VerifiedExtraction.Benchmarks.lib.Binom.
Require Import VerifiedExtraction.Benchmarks.lib.Color.
Require Import VerifiedExtraction.Benchmarks.lib.sha256.
Require Import VerifiedExtraction.Benchmarks.lib.coind.

Definition foo := 0.

Import ListNotations.
Import VeriStar.

Definition demo0 (u : unit) := [tt;tt;tt].

(* Demo 1 *)

Definition demo1 (u : unit) := List.app (List.repeat true 500) (List.repeat false 300).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 (u : unit) := List.map negb (repeat2 true false 100).

(* Demo 3 *)

Definition demo3 (u : unit) := andb.

(* List sum *)

Definition list_sum (u : unit) := List.fold_left plus (List.repeat 1 100) 0.

(* Veriest *)

Definition vs_easy (u : unit) :=
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0 =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment example_ent in
       loop n res
     end) 100  Valid.

Definition vs_hard (u : unit) :=
  match vs.main_h tt with
  | Valid => true
  | _ => false
  end.

(* Binom *)

Definition binom (u : unit) := Binom.main u.

(* Color *)
Definition color (u : unit) := Color.main u.
Time Compute color tt.

(* Lazy factorial. Needs coinductive types *)

(* Definition lazy_factorial := coq_msg_info (string_of_Z (coind.lfact 150)). *)

(* Sha *)

(* From the Rocq website *)
Definition test := "Rocq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%string.

Definition sha (u : unit) := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast (u : unit) := sha256.SHA_256' (sha256.str_to_bytes test).
