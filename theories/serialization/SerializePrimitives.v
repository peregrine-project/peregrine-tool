From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require PrimInt63.
From Stdlib Require PrimFloat.
From CeresBS Require Import Ceres.

From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Primitive.
From MetaRocq.Erasure Require Import EPrimitive.
From Peregrine Require Import CeresExtra.

Import ListNotations.
Local Open Scope bs_scope.



(** * Axioms *)
(* Realized in extraction *)
Axiom string_of_prim_int : PrimInt63.int -> string.
Axiom string_of_prim_float : PrimFloat.float -> string.
Axiom string_of_prim_string : PrimString.string -> string.


(** * Serializers *)

Instance Serialize_prim_tag : Serialize prim_tag :=
  fun t =>
    match t with
    | primInt => Atom "primInt"
    | primFloat => Atom "primFloat"
    | primString => Atom "primString"
    | primArray => Atom "primArray"
    end%sexp.

Instance Serialize_prim_int : Serialize PrimInt63.int :=
  fun i => Atom (Str (string_of_prim_int i)).

Instance Serialize_prim_float : Serialize PrimFloat.float :=
  fun f => Atom (Str (string_of_prim_float f)).

Instance Serialize_prim_string : Serialize PrimString.string :=
  fun s => Atom (Str (string_of_prim_string s)).

Instance Serialize_array_model {T : Set} `{Serialize T} : Serialize (array_model T) :=
  fun a =>
    [ Atom "array_model"; to_sexp (array_default a); to_sexp (array_value a) ]%sexp.

Instance Serialize_prim_val {T : Set} `{Serialize T} : Serialize (prim_val T) :=
  fun p =>
    let t := prim_val_tag p in
    match prim_val_model p with
    | primIntModel i => to_sexp (t, i)
    | primFloatModel f => to_sexp (t, f)
    | primStringModel s => to_sexp (t, s)
    | primArrayModel a => to_sexp (t, a)
    end.



(** * Main serialization functions *)

Definition string_of_prim_tag (t : prim_tag) : string :=
  @to_string prim_tag Serialize_prim_tag t.

Definition string_of_prim_int' (i : PrimInt63.int) : string :=
  @to_string PrimInt63.int Serialize_prim_int i.

Definition string_of_prim_float' (f : PrimFloat.float) : string :=
  @to_string PrimFloat.float Serialize_prim_float f.

Definition string_of_prim_string' (s : PrimString.string) : string :=
  @to_string PrimString.string Serialize_prim_string s.

Definition string_of_array_model {T : Set} `{Serialize T} (a : array_model T) : string :=
  @to_string (array_model T) Serialize_array_model a.

Definition string_of_prim_val {T : Set} `{Serialize T} (p : prim_val T) : string :=
  @to_string (prim_val T) Serialize_prim_val p.
