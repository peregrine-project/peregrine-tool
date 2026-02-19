From Stdlib Require Import ssreflect.
From Stdlib Require Import ZArith Floats.
From MetaRocq.Utils Require Import bytestring ReflectEq.
From MetaRocq.Common Require Import Kernames. 

Module Int63 := Numbers.Cyclic.Int63.Uint63.
Notation int := Int63.int.

(* type inttype = [`Int | `Int32 | `Int64 | `Bigint] *)
Inductive inttype : Set :=
| Int : inttype
| Int32 : inttype
| Int64 : inttype
| Bigint : inttype.

(* type numtype = [inttype | `Float64] *)
Inductive numtype : Set :=
| embed_inttype : inttype -> numtype
| Float64 : numtype.

(* type numconst = [`Int of int | `Int32 of Int32.t | `Int64 of Int64.t | `Bigint of Z.t | `Float64 of float] *)
Inductive numconst :=
| numconst_Int of int
(* | numconst_Int32 of Int32.t *)
(* | numconst_Int64 of Int64.t *)
| numconst_Bigint of Z
| numconst_Float64 of float.

(* type unary_num_op = *)
(*   [`Neg | `Not] *)

Inductive unary_num_op : Set := Neg | Not.

(* type binary_arith_op = [ `Add | `Sub | `Mul | `Div | `Mod ] *)
Inductive binary_arith_op := Add | Sub | Mul | Div | Mod.

(* type binary_bitwise_op = [ `And | `Or | `Xor | `Lsl | `Lsr | `Asr ] *)
Inductive binary_bitwise_op := And | Or | Xor | Lsl | Lsr | Asr.

(* type binary_comparison = [ `Lt | `Gt | `Lte | `Gte | `Eq ] *)
Inductive  binary_comparison := Lt | Gt | Lte | Gte | Eq.

(* type binary_num_op = *)
(*   [ binary_arith_op | binary_bitwise_op | binary_comparison ] *)
Inductive binary_num_op :=
  embed_binary_arith_op of binary_arith_op | embed_binary_bitwise_op of binary_bitwise_op | embed_binary_comparison of binary_comparison.

(* type vector_type = *)
(*   [`Array | `Bytevec] *)
Inductive vector_type := Array | Bytevec.

(* type mutability = *)
(*   [ `Imm | `Mut ] *)
Inductive mutability := Inm | Mut.

(* type block_tag = int *)
Definition block_tag := int.

(* type case = [`Tag of int | `Deftag | `Intrange of int * int] *)
Inductive case := Tag of int | Deftag | Intrange of int * int.

(* let max_tag = 200 *)
(* let tag_of_int n = *)
(*   if 0 <= n && n < max_tag then *)
(*     n *)
(*   else *)
(*     invalid_arg "tag out of range" *)

(* Definition max_tag : int := Int63.of_Z 200. *)
(* Axiom invalid_arg : forall {A}, string -> A. *)
(* Definition tag_of_int n := *)
(*   if Int63.leb (Int63.of_Z 0) n && Int63.ltb n max_tag then *)
(*     n *)
(*   else *)
(*     invalid_arg "tag out of range". *)


Module Ident.
  Definition t := string.
  Definition eqb (x y : t) := x == y.

  Module Map.
    Section fix_A.
    Context {A : Type}.

    Definition t := Ident.t -> A.

    Definition add (x : Ident.t) (v : A) (locals : t)  :=
      fun y =>
        if Ident.eqb y x then v else locals y.

    Definition find (x : Ident.t) (locals : t) :=
      locals x.
    End fix_A.
  End  Map.

End Ident.

Module Longident.
  Definition t := string.
End Longident.

Section list_notation.
Local Notation "A 'list'" := (list A) (at level 4).
(* type t = *)
Inductive t :=
| Mvar of Ident.t
| Mlambda of Ident.t list * t
| Mapply of t * t list
| Mlet of binding list * t
| Mnum of numconst
| Mstring of string
| Mglobal of Longident.t
| Mswitch of t * (case list * t) list

(* Numbers *)
| Mnumop1 of unary_num_op * numtype * t
| Mnumop2 of binary_num_op * numtype * t * t
| Mconvert of numtype * numtype * t

(* Vectors *)
| Mvecnew of vector_type * t * t
| Mvecget of vector_type * t * t
| Mvecset of vector_type * t * t * t
| Mveclen of vector_type * t

(* Lazy *)
| Mlazy of t
| Mforce of t

(* Blocks *)
| Mblock of int * t list
| Mfield of int * t
with binding :=
| Unnamed of t | Named of Ident.t * t | Recursive of (Ident.t * t) list.
End list_notation.

Definition var := Ident.t.

Definition module := list (Malfunction.Ident.t * t).
Definition program : Type := list (Ident.t * option t) * t.

Inductive prim_def (id : Type) := 
 | Global (modname : id) (label : id)
 | Primitive (symbol : string) (arity : nat)
 | Erased.
Arguments Global {id}.
Arguments Primitive {id}.
Arguments Erased {id}.

Definition primitives := list (bytestring.string * prim_def bytestring.string).
