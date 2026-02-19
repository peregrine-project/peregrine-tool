From Equations Require Import Equations.
From Malfunction Require Import FFI.
From VerifiedExtraction Require Import Extraction OCamlFFI.
From MetaRocq.Template Require Import All.
From Stdlib Require ZArith Streams.StreamMemo.

From Stdlib Require Import String.
From Stdlib Require Vector.

(* Set Verified Extraction Build Directory "_build". *)
(* Set Verified Extraction Opam Path "/usr/local/bin/opam". *)

From Stdlib Require Import PrimInt63 Sint63.
Definition test_primint := 
  let _ := print_int Sint63.min_int in
  let _ := print_newline tt in
  let _ := print_int Sint63.max_int in tt.
Eval compute in test_primint.

Verified Extraction (plus, mult).

Verified Extraction -fmt -compile-with-coq -run test_primint "test_primint.mlf".

From Stdlib Require Import PrimFloat.
Definition test_floats := print_float (100.5)%float.
Eval compute in test_floats.
Verified Extraction -fmt -compile-with-coq -run test_floats "test_floats.mlf".

(* Lazy cofixpoint implentation *)

Module NegativeCoind.
Set Primitive Projections.
CoInductive stream := Cons
  { head : nat; tail : stream }.

Fixpoint take (n : nat) (s : stream) : list nat :=
  match n with
  | 0 => []
  | S n => s.(head) :: take n s.(tail)
  end.
  
CoFixpoint ones : stream := {| head := 1; tail := ones |}.

Definition test_ones := print_string (show (take 10 ones)).

Verified Extraction -fmt -unsafe -compile-with-coq -run test_ones "ones.mlf".

CoFixpoint naturals (n : nat) : stream := 
  {| head := n; tail := naturals (S n) |}.

Verified Extraction -fmt -unsafe naturals.

Definition test_take := print_string (show (take 10 (naturals 0))).

Verified Extraction -fmt -unsafe -compile-with-coq -run test_take "naturals.mlf".

Import ZArith Streams.StreamMemo.
Local Open Scope Z_scope.
Fixpoint tfact (n: nat) :=
  match n with
   | O => 1
   | S n1 => Z.of_nat n * tfact n1
  end.

Definition lfact_list :=
  dimemo_list _ tfact (fun n z => (Z.of_nat (S  n) * z)).

Definition lfact n := dmemo_get _ tfact n lfact_list.

Theorem lfact_correct n: lfact n = tfact n.
Proof.
unfold lfact, lfact_list.
rewrite dimemo_get_correct; auto.
Qed.

Fixpoint nop p :=
  match p with
   | xH => 0
   | xI p1 => nop p1
   | xO p1 => nop p1
  end.

Definition test z :=
  match z with
   | Z0 => 0
   | Zpos p1 => nop p1
   | Zneg p1 => nop p1
  end.

(*  
Time Eval vm_compute in test (lfact 2000). (* 4.7s *)
Time Eval vm_compute in test (lfact 2000). (* Immediate due to sharing?? *)
Time Eval vm_compute in test (lfact 1500).
Time Eval vm_compute in (lfact 1500). (* 20s *) *)
Arguments print_string s%bs.
Definition arg := 1000%nat.
Definition test_lfact := test (lfact arg).
Definition show_lfact := print_string ("test_lfact: " ++ show (lfact arg)).
(* Set Debug "verified-extraction". *)

Verified Extraction -time -fmt -typed -unsafe -compile-with-coq -run test_lfact "test_lfact_typed.mlf". (* 2.5s running time *)
Verified Extraction -time -fmt -unsafe -compile-with-coq -run test_lfact "test_lfact.mlf". (* 2.5s running time *)
Verified Extraction -optimize -time -fmt -typed -unsafe -compile-with-coq -run 
  test_lfact "test_lfact_typed_opt.mlf". (* 2.5s running time *)

Verified Extraction -time -fmt -typed -unsafe -compile-with-coq -run 
  show_lfact "show_lfact_typed.mlf". (* 3.4s running time *)
Verified Extraction -time -fmt -unsafe -compile-with-coq -run 
  show_lfact "show_lfact.mlf". (* 3.4s running time *)

End NegativeCoind.

Module Unboxed.

  Definition t := { x : nat | x < 3 }.
  Program Definition ex : t := 1.
  Program Definition test_ex := coq_msg_info (string_of_nat ex).

  Verified Extraction -typed -unsafe -fmt -compile-plugin -run test_ex "test_ex.mlf".
End Unboxed.


(** Typed extraction *)

Definition sub : { x : nat | x = 0 } := @exist _ _ 0 eq_refl.
Verified Extraction sub.
Verified Extraction -typed sub.

Equations idnat (n : nat) : nat by wf n lt :=
 | 0 => 0
 | S n => S (idnat n).

Extraction idnat.

Verified Extract Inline [ Equations.Prop.Subterm.FixWf, Corelib.Init.Wf.Fix, Corelib.Init.Wf.Fix_F, idnat_functional ].

Verified Extraction -fmt -unsafe -typed idnat "idnat.mlf".

Inductive three := ZERO | ONE | TWO | THREE.

Definition two := TWO.

From MetaRocq.Utils Require Import bytestring.

Definition test_bytestring (u : unit) := bytestring.String.compare "" "bug".

Verified Extraction -compile-with-coq test_bytestring "test_bytestring.mlf".

Verified Extraction two "two.mlf".

Axiom axiom : nat.

Verified Extraction axiom "axiom.mlf".

From Malfunction Require Import Compile Pipeline.

From Stdlib Require Import List.
Import ListNotations.

Polymorphic Record myprod@{i j} (A : Type@{i}) (B : Type@{j}) := mypair { fst : A; snd : B }.

Notation "( x , y , .. , z )" := (mypair _ _ .. (mypair _ _ x y) .. z) : core_scope.
Definition many_list_functions : myprod _ _ := (@List.firstn nat, @List.filter nat, @List.skipn nat).

Verified Extraction -fmt -typed many_list_functions "list.mlf".

Definition prf := match conj I I with conj x y => (x,0) end.

Verified Extraction prf "proof.mlf".

Verified Extraction blocks_until "mcase.mlf".

Definition test_add := plus 2 5.

Verified Extraction test_add "add.mlf".

Verified Extraction (match cons THREE nil with cons x _ => x | _ => ONE end).
Verified Extraction -help.

Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.

Verified Extraction (ack 3 5).

Verified Extraction (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

Verified Extraction vplus0123.

Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Arguments leaf {A}.
Arguments fcons {A}.
Arguments node {A}.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).

Verified Extraction (forest_size arden).
