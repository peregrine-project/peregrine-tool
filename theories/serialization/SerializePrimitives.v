From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require PrimInt63.
From Stdlib Require PrimFloat.
From Corelib Require Uint63Axioms PrimStringAxioms.
From CeresBS Require Import Ceres.

From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Primitive.
From MetaRocq.Erasure Require Import EPrimitive.

Import ListNotations.
Local Open Scope bs_scope.



(** * Primitive strings *)

(** Bytes of a primitive string; its characters are always below 256
    ([PrimStringAxioms.to_list_char63_valid]), so the default case is unreachable. *)
Definition byte_of_char63 (c : PrimInt63.int) : Byte.byte :=
  match Byte.of_N (Z.to_N (Uint63Axioms.to_Z c)) with
  | Some b => b
  | None => Byte.x00
  end.

(* Realized in extraction by [Pstring.to_string]. *)
Definition string_of_prim_string (s : PrimString.string) : string :=
  String.parse (List.map byte_of_char63 (PrimStringAxioms.to_list s)).


(** * Serializers *)

Instance Serialize_prim_tag : Serialize prim_tag :=
  fun t =>
    match t with
    | primInt => Atom "primInt"
    | primFloat => Atom "primFloat"
    | primString => Atom "primString"
    | primArray => Atom "primArray"
    end%sexp.

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
  @to_string PrimInt63.int (@Serialize_Integral PrimInt63.int Integral_sint) i.

Definition string_of_prim_float' (f : PrimFloat.float) : string :=
  @to_string PrimFloat.float Serialize_prim_float f.

Definition string_of_prim_string' (s : PrimString.string) : string :=
  @to_string PrimString.string Serialize_prim_string s.

Definition string_of_array_model {T : Set} `{Serialize T} (a : array_model T) : string :=
  @to_string (array_model T) Serialize_array_model a.

Definition string_of_prim_val {T : Set} `{Serialize T} (p : prim_val T) : string :=
  @to_string (prim_val T) Serialize_prim_val p.
