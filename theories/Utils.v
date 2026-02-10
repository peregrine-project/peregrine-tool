From Stdlib Require Import List.
From MetaRocq.Utils Require Import bytestring.

Import ListNotations.

Local Open Scope bs_scope.



Fixpoint filter_map {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x l' =>
    match f x with
    | Some x' => x' :: filter_map f l'
    | None => filter_map f l'
    end
  end.

Definition split (sep : Byte.byte) (s : string) : list string :=
  let fix aux s :=
    match s with
    | String.EmptyString => ("", [])
    | String.String b t =>
      let '(s', l) := aux t in
      if (Byte.eqb b sep)%bs then ("", s' :: l) else (String.String b s', l)%bs
    end in
  let '(s', l) := aux s in
  s' :: l.

Fixpoint last {A : Type} (l : list A) (d : A) : list A * A :=
  match l with
  | [] => ([], d)
  | [a] => ([], a)
  | a :: l =>
    let '(l, x) := last l d in
    (a :: l, x)
  end.

Definition split_name (s : string) : string * string :=
  let l := split "." s in
  let '(l, s) := last l "" in
  (String.concat "." l, s).
