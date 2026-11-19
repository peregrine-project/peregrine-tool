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

Definition char63_of_byte (b : Byte.byte) : PrimInt63.int :=
  Uint63Axioms.of_Z (Z.of_N (Byte.to_N b)).

(** [None] if the string is longer than [PrimString.max_length].
    Realized in extraction by [Pstring.of_string]. *)
Definition prim_string_of_string (s : string) : option PrimString.string :=
  if (Z.of_nat (String.length s) <=? Uint63Axioms.to_Z PrimString.max_length)%Z
  then Some (PrimStringAxioms.of_list (List.map char63_of_byte (String.print s)))
  else None.



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

Instance Deserialize_prim_string : Deserialize PrimString.string :=
  fun l e =>
    match e with
    | Atom_ (Str s) =>
        match prim_string_of_string s with
        | Some p => inr p
        | None => inl (DeserError l "string too long for a primitive string")
        end
    | _ => inl (DeserError l "error")
    end.

(* The generic, combinator-based deserializer for [array_model]. *)
Definition Deserialize_array_model_gen {T : Set} `{Deserialize T} : Deserialize (array_model T) :=
  fun l e =>
    Deser.match_con "array_model" []
      [ ("array_model", Deser.con2_ Build_array_model) ]
      l e.

(* The instance is the combinator-based deserializer with the Ceres
   combinators unfolded at definition time.
   [Deserialize_array_model] is used nested inside the fixpoint
   [deserialize_term] (through [Deserialize_prim_val]) with the recursive
   function as instance for [T]. Rocq's guard checker re-checks an argument
   containing an unapplied recursive call once per combinator it is passed
   through, so nesting a second [Deser.match_con] inside the one of
   [deserialize_term] multiplies the checking time by a large factor (~75s
   instead of ~1s). With the combinators already unfolded there is nothing
   left to expand. *)
Instance Deserialize_array_model {T : Set} `{Deserialize T} : Deserialize (array_model T) :=
  ltac:(let t := eval cbv [Deserialize_array_model_gen Deser.match_con Deser._con
                           Deser.con2_ Deser.con2 Deser.fields Deser.bind_field Deser.ret
                           _fields List.map fst CeresUtils._find_or CeresUtils._bind_sum]
                 in (@Deserialize_array_model_gen T _) in
        exact t).

Lemma Deserialize_array_model_eq {T : Set} `{Deserialize T} l e :
  @_from_sexp (array_model T) Deserialize_array_model l e =
  Deser.match_con "array_model" []
    [ ("array_model", Deser.con2_ Build_array_model) ]
    l e.
Proof. reflexivity. Qed.

Instance Deserialize_prim_val {T : Set} `{Deserialize T} : Deserialize (prim_val T) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      let t := @_from_sexp prim_tag _ l e1 in
      match t with
      | inr primInt =>
        let v := @_from_sexp PrimInt63.int (@Deserialize_SemiIntegral PrimInt63.int
                               SemiIntegral_sint) l e2 in
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
  @from_string PrimInt63.int (@Deserialize_SemiIntegral PrimInt63.int SemiIntegral_sint) s.

Definition prim_float_of_string' (s : string) : error + PrimFloat.float :=
  @from_string PrimFloat.float Deserialize_prim_float s.

Definition prim_string_of_string' (s : string) : error + PrimString.string :=
  @from_string PrimString.string Deserialize_prim_string s.

Definition array_model_of_string {T : Set} `{Deserialize T} (s : string) : error + (array_model T) :=
  @from_string (array_model T) Deserialize_array_model s.

Definition prim_val_of_string {T : Set} `{Deserialize T} (s : string) : error + (prim_val T) :=
  @from_string (prim_val T) Deserialize_prim_val s.
