Require Import List Uint63.
Import ListNotations.

Definition merge {T : Type} (leT : T -> T -> bool) :=
fix merge (s1 : list T) : list T -> list T :=
  match s1 with
  | [] => id
  | x1 :: s1' =>
      fix merge_s1 (s2 : list T) : list T :=
        match s2 with
        | [] => s1
        | x2 :: s2' =>
            if leT x1 x2
            then x1 :: merge s1' s2
            else x2 :: merge_s1 s2'
        end
  end.

Definition merge_sort_pop {T : Type} (leT : T -> T -> bool) :=
fix merge_sort_pop (s1 : list T) (ss : list (list T)) : list T :=
  match ss with
  | [] => s1
  | s2 :: ss' => merge_sort_pop (merge leT s2 s1) ss'
  end.

Definition merge_sort_push {T : Type} (leT : T -> T -> bool) :=
fix merge_sort_push (s1 : list T) (ss : list (list T)) :
    list (list T) :=
  match ss with
  | [] => s1 :: ss
  | [] :: ss' => s1 :: ss'
  | (_ :: _) as s2 :: ss' =>
      [] :: merge_sort_push (merge leT s2 s1) ss'
  end.

Definition merge_sort_rec {T : Type} (leT : T -> T -> bool) :=
fix merge_sort_rec (ss : list (list T)) (s : list T) : list T :=
  match s with
  | [] => merge_sort_pop leT s ss
  | [x1] => merge_sort_pop leT s ss
  | (x1 :: x2 :: s') =>
      let s1 :=
        if leT x1 x2 then [x1; x2] else [x2; x1] in
      merge_sort_rec (merge_sort_push leT s1 ss) s'
  end.

Definition sort {T : Type} (leT : T -> T -> bool) : list T -> list T :=
  merge_sort_rec leT [].

Fixpoint path {T : Type} (e : T -> T -> bool) (x : T) (p : list T) :=
  match p with
  | [] => true
  | y :: p' => andb (e x y) (path e y p')
  end.

Definition sorted {T : Type} (e : T -> T -> bool) (s : list T) :=
  match s with
  | [] => true
  | x :: s' => path e x s'
  end.

Fixpoint inintlist (x : int) (l : list int) : bool :=
   match l with
   | [] => false
   | y :: l' => if (x =? y)%uint63 then true else inintlist x l'
   end.

Definition append1_and_sort (s : list int) (x : int) :=
  if inintlist x s then sort Uint63.leb s
  else sort Uint63.leb (x :: s).

Definition append1_sorted (s : list int) (x : int) : list int :=
  if inintlist x s then s
  else merge Uint63.leb [x] s.

Definition append1_sorted_option (s : list int) (x : int) : option (list int) :=
  if sorted Uint63.leb s then Some (append1_sorted s x)
  else None.

From VerifiedExtraction Require Import Extraction OCamlFFI.
Set Verified Extraction Build Directory ".".

From MetaRocq.Utils Require Import bytestring.

Definition test := append1_and_sort [1%uint63] 1.
Eval compute in test.
From MetaRocq Require Import Show.
Definition append1_and_sort_test := print_string (show test).

MetaRocq Run Print mli append1_and_sort_test.
Verified Extraction -compile-with-coq -run append1_and_sort_test "append1_and_sort.mlf".
