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
Axiom prim_int_of_string : string -> PrimInt63.int.
Axiom prim_float_of_string : string -> PrimFloat.float.
Axiom prim_string_of_string : string -> PrimString.string.



(** * Deserializers *)

Instance Deserialize_prim_tag : Deserialize prim_tag :=
  fun l e =>
    Deser.match_con "prim_tag"
      [ ("primInt", primInt)
      ; ("primFloat", primFloat)
      ; ("primString", primString)
      ; ("primArray", primArray)
      ]
      [] l e.

Instance Deserialize_prim_int : Deserialize PrimInt63.int :=
  fun l e =>
    match e with
    | Atom_ (Str i) => inr (prim_int_of_string i)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_prim_float : Deserialize PrimFloat.float :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr (prim_float_of_string s)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_prim_string : Deserialize PrimString.string :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr (prim_string_of_string s)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_array_model {T : Set} `{Deserialize T} : Deserialize (array_model T) :=
  fun l e =>
    Deser.match_con "array_model" []
      [ ("array_model", con2_ Build_array_model) ]
      l e.

Instance Deserialize_prim_val {T : Set} `{Deserialize T} : Deserialize (prim_val T) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      let t := @_from_sexp prim_tag _ l e1 in
      match t with
      | inr primInt =>
        let v := @_from_sexp PrimInt63.int _ l e2 in
        match v with
        | inr v => inr (prim_int v)
        | inl e => inl e
        end
      | inr primFloat =>
        let v := @_from_sexp PrimFloat.float _ l e2 in
        match v with
        | inr v => inr (prim_float v)
        | inl e => inl e
        end
      | inr primString =>
        let v := @_from_sexp PrimString.string _ l e2 in
        match v with
        | inr v => inr (prim_string v)
        | inl e => inl e
        end
      | inr primArray =>
        let v := @_from_sexp (array_model T) _ l e2 in
        match v with
        | inr v => inr (prim_array v)
        | inl e => inl e
        end
      | inl e => inl e
      end
    | _ => inl (DeserError l "error")
    end.



(** * Main deserialization functions *)

Definition prim_tag_of_string (s : string) : error + prim_tag :=
  @from_string prim_tag Deserialize_prim_tag s.

Definition prim_int_of_string' (s : string) : error + PrimInt63.int :=
  @from_string PrimInt63.int Deserialize_prim_int s.

Definition prim_float_of_string' (s : string) : error + PrimFloat.float :=
  @from_string PrimFloat.float Deserialize_prim_float s.

Definition prim_string_of_string' (s : string) : error + PrimString.string :=
  @from_string PrimString.string Deserialize_prim_string s.

Definition array_model_of_string {T : Set} `{Deserialize T} (s : string) : error + (array_model T) :=
  @from_string (array_model T) Deserialize_array_model s.

Definition prim_val_of_string {T : Set} `{Deserialize T} (s : string) : error + (prim_val T) :=
  @from_string (prim_val T) Deserialize_prim_val s.
