From MetaRocq.Utils Require Import Show.
From MetaRocq.Template Require Import Loader.
From MetaRocq.ErasurePlugin Require Import Loader.
From VerifiedExtraction Require Import Extraction OCamlFFI.
From MetaRocq.Template Require Import All.

From Stdlib Require Import ZArith PrimInt63 Sint63.
Eval compute in PrimInt63.ltb Sint63.min_int Sint63.min_int.

Set Warnings "-primitive-turned-into-axiom".

Definition test := print_int ( Sint63.max_int).
Verified Extraction -fmt -verbose -compile-with-coq -run test "test.mlf".
Verified Extraction -verbose Sint63.min_int.
Verified Extraction -verbose Uint63.max_int.

Definition max_to_Z := print_string (string_of_Z (Uint63.to_Z Uint63.max_int)).
Verified Extraction -verbose -compile-with-coq -run max_to_Z "max_to_Z.mlf".

Definition check_lt := print_string (show (PrimInt63.ltb 1 0)).
Verified Extraction -compile-with-coq -run check_lt "check_lt.mlf".

From Stdlib Require Import PrimFloat.
Definition test_float := print_float (7500.50)%float.
Eval compute in FloatOps.Prim2SF 75000.5%float.
Verified Extraction -fmt -compile-with-coq -run test_float "test_float.mlf".

From Stdlib Require Import PArray.
From Malfunction Require Import utils_array.

Definition val : array nat := PArray.make 3 2.

Definition gettest : nat := PArray.get val 2. 
Definition settest : array nat := PArray.set val 2 1. 
Definition getsettest : nat := PArray.get settest 2.

Set Warnings "-primitive-turned-into-axiom".

Definition prim_array_get := (print_int (int_of_nat gettest)).
Definition prim_array_get_set := (print_int (int_of_nat getsettest)).

Verified Extraction -fmt -typed -compile-with-coq val "val.mlf".
(* TODO Matthieu 
Verified Extraction -fmt -typed -compile-with-coq -run prim_array_get "prim_array_get.mlf".
Verified Extraction -fmt -typed -compile-with-coq -run prim_array_get_set "prim_array_get_set.mlf".
*)

(*
Open Scope bs.

From MetaRocq.Common Require Import Kernames.

From Stdlib Require Import String.
From Stdlib Require Vector.

Inductive three := ZERO | ONE | TWO | THREE.

Definition two := TWO.

Open Scope bs.

From Stdlib Require Import Uint63.xfg+

Verified Extraction max_int.

Verified Extraction two "two.mlf".

Axiom axiom : nat.

Verified Extraction axiom "axiom.mlf".

Definition testAAAAA := 0.
Definition test := testAAAAA.

Verified Extraction test.

Definition testA := 0.

Definition many_list_functions := (@List.firstn, @List.filter, @List.skipn).

Verified Extraction many_list_functions "list.mlf".

Definition prf := match conj I I with conj x y => (x,0) end.

Verified Extraction prf "proof.mlf".

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

Definition bla {A} (a : A) (b : bool) : b = true -> A :=
  match b with
  | true => fun _ => a
  | false => fun E => match E with end
  end.

Verified Extraction @Vector.nil.

Verified Extraction @Vector.cons.

Definition case0 {A} (P:Vector.t A 0 -> Type) (H:P (Vector.nil A)) v:P v :=
match v with
  |Vector.nil => H
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

From Stdlib Require Import VectorDef.


Verified Extraction @t_rec.

Definition vtest := @VectorDef.rectS.

Verified Extraction @VectorDef.case0.

Verified Extraction vtest.

Arguments Vector.case0 : clear implicits.

Verified Extraction Vector.case0.

Verified Extraction (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

Verified Extraction @Vector.hd.

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
*)