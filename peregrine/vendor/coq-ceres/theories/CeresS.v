(** * S-expressions *)

(* begin hide *)
From Stdlib Require Import
  DecidableClass List ZArith Strings.Byte (* Ascii String *).
From MetaRocq.Utils Require Import bytestring.

From Ceres Require Import
  CeresString.

Unset Elimination Schemes.
(* end hide *)

(** S-expressions, parameterized by the type of atoms. *)
Inductive sexp_ (A : Type) :=
| Atom_ (a : A)
| List (xs : list (sexp_ A))
.

Arguments Atom_ {A} a.
Arguments List {A} xs.

(* Declare Scope sexp_scope. *)
Declare Scope sexp_scope.
Delimit Scope sexp_scope with sexp.
Bind Scope sexp_scope with sexp_.

Notation "[ ]" := (List nil) : sexp_scope.
Notation "[ x ]" := (List (@cons (sexp_ _) x nil)) : sexp_scope.
Notation "[ x ; y ; .. ; z ]"
  := (List (@cons (sexp_ _) x (@cons (sexp_ _) y .. (@cons (sexp_ _) z nil) .. )))
  : sexp_scope.

(** Apply a function to every atom. *)
Fixpoint map_sexp_ {A B : Type} (f : A -> B) (x : sexp_ A) : sexp_ B :=
  match x with
  | Atom_ a => Atom_ (f a)
  | List xs => List (map (map_sexp_ f) xs)
  end.

(** Replace every atom with an S-expression. *)
Fixpoint subst_sexp_ {A B : Type} (f : A -> sexp_ B) (x : sexp_ A) : sexp_ B :=
  match x with
  | Atom_ a => f a
  | List xs => List (map (subst_sexp_ f) xs)
  end.

(** Construct an S-expression from a list of atoms. *)
Definition sexp_of_atoms {A} (xs : list A) : sexp_ A :=
  List (map Atom_ xs).

(** * Default atoms *)

(** Default type of atoms. [sexp_ atom] thus provides a uniform format to
    store and exchange semi-structured data. *)
Variant atom : Set :=
| Num (n : Z)       (* Integers. *)
| Str (s : string)  (* Literal strings. *)
| Raw (s : string)  (* Simple atoms (e.g., ADT tags). *)
                    (* Should fit in this alphabet: [A-Za-z0-9-_.']. *)
.

Notation sexp := (sexp_ atom).
Notation Atom := (@Atom_ atom).  (* This notation helps make coercions work. *)

(** Potential future extensions: binary strings, floating-point *)

(** *** Coercions and notations *)

Coercion Num : Z >-> atom.
Coercion Raw : string >-> atom.

(** ** Destructors *)

(** This interface deliberately lacks a way to exhaustively eliminate an
    [atom] to enable backward compatible extensions. *)

Definition get_Num (a : atom) : option Z :=
  match a with
  | Num n => Some n
  | _ => None
  end.

Definition get_Str (a : atom) : option string :=
  match a with
  | Str s => Some s
  | _ => None
  end.

Definition get_Raw (a : atom) : option string :=
  match a with
  | Raw s => Some s
  | _ => None
  end.

(** ** Equality *)

(* The inductive type [sexp] has recursive occurences
   nested in [list : Type -> Type].

   A common formula to define a recursive function [f_sexp] on [sexp]
   (here, [eqb_sexp]) is to first define a recursive function
   [f_list] on [list A] parameterized by a function [f] on [A],
   which is going to be [f_sexp] in the definition of [f_sexp].

   There are some more details to be careful about in order to make
   the definition of [f_sexp] well-founded. In [f_list], the
   parameter [f] should be bound _outside_ of the [fix]
   expression, which only binds lists, ensuring that when the
   definition of [f_list] is unfolded in [f_sexp], [f] gets
   substituted with recursive occurences of [f_sexp].
 *)

Definition eqb_list {A B} (f : A -> B -> bool)
  : list A -> list B -> bool :=
  fix eqb_list_ (xs : list A) (ys : list B) :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => (f x y && eqb_list_ xs ys)%bool
    | _, _ => false
    end%list.

Definition eqb_sexp_ {A B} (a_eqb : A -> B -> bool)
  : sexp_ A -> sexp_ B -> bool :=
  fix eqb_sexp__ (s1 : sexp_ A) (s2 : sexp_ B) : bool :=
    match s1, s2 with
    | Atom_ a1, Atom_ a2 => a_eqb a1 a2
    | List xs1, List xs2 => eqb_list eqb_sexp__ xs1 xs2
    | _, _ => false
    end.

Definition eqb_atom (x1 x2 : atom) : bool :=
  match x1, x2 with
  | Raw s1, Raw s2 => eqb_string s1 s2
  | Str s1, Str s2 => eqb_string s1 s2
  | Num z1, Num z2 => Z.eqb z1 z2
  | _, _ => false
  end.

Definition eqb_sexp : sexp -> sexp -> bool :=
  eqb_sexp_ eqb_atom.

Ltac magic :=
  simpl in *;
  repeat
    match goal with
    | [ H : Forall _ (cons _ _) |- _ ] => inversion_clear H
    | [ |- andb _ _ = true ] => apply andb_true_intro
    | [ H : cons ?x ?xs = cons ?y ?ys |- _ ] => inversion H; clear H; subst
    | [ H : ?t = true |- _ ] =>
      match t with
      | andb _ _ => apply andb_prop in H; destruct H
      | Z.eqb _ _ => apply Z.eqb_eq in H; subst
      | eqb_string _ _ => apply eqb_eq_string in H; subst
      end
    | [ H : _ |- _ ] => solve [ apply H; auto ]
    end; auto.

Lemma eqb_eq_list {A} (eqb : A -> A -> bool) (xs : list A)
      (Heqb : Forall (fun a : A => forall b : A, eqb a b = true <-> a = b) xs)
  : forall (xs' : list A), eqb_list eqb xs xs' = true <-> xs = xs'.
Proof with auto.
  induction xs; intros []; split; intros; try discriminate;
    magic; [ f_equal | split ]; magic.
Defined.

Lemma eqb_eq_atom : eqb_eq eqb_atom.
Proof with auto.
  split; intros.
  - destruct a, b; try discriminate; magic.
  - subst; destruct b; simpl; try apply Z.eqb_refl; try apply eqb_eq_string...
Defined.

Global
Instance Decidable_eq_atom : forall (x1 x2 : atom), Decidable (x1 = x2).
Proof.
  exact (fun x1 x2 =>
           {| Decidable_witness := eqb_atom x1 x2;
              Decidable_spec := eqb_eq_atom x1 x2 |}).
Defined.

Lemma forall_Forall : forall {X} (P : X -> Prop),
    (forall x, P x) -> forall (xs : list X), Forall P xs.
Proof. intros; induction xs; auto. Defined.

Lemma sexp__ind : forall (A : Type) (P : sexp_ A -> Prop),
    (forall a : A, P (Atom_ a)) ->
    (forall xs : list (sexp_ A), Forall P xs -> P (List xs)) ->
    forall s : sexp_ A, P s.
Proof.
  intros A P Ha Hxs.
  fix self 1.
  intros [].
  - auto.
  - apply Hxs.
    apply forall_Forall.
    assumption.
Defined.

Lemma eqb_eq_sexp_ {A} {eqb_A : A -> A -> bool}
      (Heqb_eq : eqb_eq eqb_A) : eqb_eq (eqb_sexp_ eqb_A).
Proof with auto.
  intro s1.
  induction s1; intros []; split; intro HH; try discriminate; try injection HH; intros.
  1,2: try f_equal; apply Heqb_eq; auto.
  - f_equal; simpl in *; apply eqb_eq_list in HH...
  - simpl; eapply eqb_eq_list; auto.
Defined.

Definition eqb_eq_sexp : eqb_eq eqb_sexp := eqb_eq_sexp_ eqb_eq_atom.

Global
Instance Decidable_eq_sexp : forall (s1 s2 : sexp), Decidable (s1 = s2).
Proof.
  exact (fun s1 s2 =>
           {| Decidable_witness := eqb_sexp s1 s2;
              Decidable_spec := eqb_eq_sexp s1 s2 |}).
Defined.

(** ** Example *)
Section Example.
Import ListNotations.

Local Open Scope bs_scope.

(** This S-expression:

<<
(example
  (message "I'm a teapot")
  (code 418))
>>

corresponds to this [sexp] in Gallina:
*)

Let example_1 : sexp :=
  List [ Atom "example"
       ; List [ Atom "message" ; Atom (Str "I'm a teapot") ]
       ; List [ Atom "code" ; Atom 418%Z ]
       ].

Local Open Scope sexp.

(** Or, overloading the list notation... *)

Let example_2 : sexp :=
  [ Atom "example"
  ; [ Atom "message" ; Atom (Str "I'm a teapot") ]
  ; [ Atom "code" ; Atom 418%Z ]
  ].

End Example.
