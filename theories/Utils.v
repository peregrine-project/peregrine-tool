From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require EWellformed.

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



Definition assert {E : Type} (b : bool) (e : E) : result unit E :=
  if b then Ok tt else Err e.

Definition assert' {E : Type} (b : bool) (s : unit -> E) : result unit E :=
  if b then Ok tt else Err (s tt).

Definition result' T : Type := result T string.

Definition assert_some {A : Type} (b : option A) (s : unit -> string) : result' unit :=
  match b with
  | Some _ =>  Ok tt
  | None => Err (s tt)
  end.

Import MonadNotation.

Definition result_forall {A : Type} (f : A -> result' unit) (l : list A) :=
  List.fold_left (fun a t => a ;; f t) l (Ok tt).

Definition bool_of_result {T E : Type} (r : result T E) : bool :=
  match r with
  | Ok _ => true
  | Err _ => false
  end.

Lemma result_mapb {E1 E2 T : Type} : forall (f : E1 -> E2) (r : result T E1),
  bool_of_result (map_error f r) = bool_of_result r.
Proof.
  intros.
  destruct r; reflexivity.
Qed.

Lemma result_assertb' {E : Type} : forall b (s : unit -> E),
  bool_of_result (assert' b s) = b.
Proof.
  intros.
  destruct b; reflexivity.
Qed.

Lemma result_assertb : forall b s (c : result' unit),
  bool_of_result (assert b s ;; c) = b && (bool_of_result c).
Proof.
  intros.
  destruct b; reflexivity.
Qed.

Lemma result_assert_someb' {A : Type} : forall (o : option A) s,
  bool_of_result (assert_some o s) = EWellformed.isSome o.
Proof.
  intros.
  destruct o; reflexivity.
Qed.

Lemma result_assert_someb {A : Type} : forall (o : option A) s (c : result' unit),
  bool_of_result (assert_some o s ;; c) = EWellformed.isSome o && (bool_of_result c).
Proof.
  intros.
  destruct o; reflexivity.
Qed.

Lemma result_bindb {T E: Type} : forall (c1 c2 : (fun T => result T E) T),
  bool_of_result (c1 ;; c2) = bool_of_result c1 && bool_of_result c2.
Proof.
  intros.
  destruct c1, c2; reflexivity.
Qed.

Lemma result_forallb' {A : Type} : forall (f : A -> result' unit)  h (t : list A),
  bool_of_result (fold_left (fun a t => a ;; f t) (h :: t) (Ok tt)) =
  bool_of_result (f h) && bool_of_result (fold_left (fun a t => a ;; f t) t (Ok tt)).
Proof.
  intros.
  cbn.
  destruct (f h); simpl.
  - destruct t0.
    reflexivity.
  - induction t.
    + reflexivity.
    + cbn.
      apply IHt.
Qed.

Lemma result_forallb {A : Type} : forall f f' (l : list A),
  (forall x, bool_of_result (f x) = f' x) ->
  bool_of_result (result_forall f l) = forallb f' l.
Proof.
  induction l; auto.
  intros.
  unfold result_forall in *.
  rewrite result_forallb'.
  rewrite H.
  rewrite IHl by assumption.
  reflexivity.
Qed.

Lemma result_forall_allb {A : Type} : forall f f' (l : list A),
  All (fun x => bool_of_result (f x) = f' x) l ->
  bool_of_result (result_forall f l) = forallb f' l.
Proof.
  induction l; auto.
  intros.
  unfold result_forall in *.
  rewrite result_forallb'.
  inversion X; subst.
  rewrite H0.
  rewrite IHl by assumption.
  reflexivity.
Qed.
