(** Natural numbers on Koka's [int] for the typed Koka backend (verb
    [koka-typed-int]): an [int] is a tagged small integer with a big-integer
    fallback, the representation [rust-hybrid] builds by hand.

    The entry for [nat] itself selects the native representation in the printer
    ([PrintKokaTyped.is_native]): [O] is [0], [S x] is [x + 1], and a match
    becomes a match on [0] that binds the predecessor.  The other entries are
    the operations.  Like every remapping, they are trusted, not verified. *)

From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.
From TypedExtraction Require Import Common.
From Stdlib Require Import Arith List.
Import ListNotations.

Local Open Scope bs_scope.

Definition koka_const (arity : nat) (s : string) : remapped_constant := {|
  re_const_ext := None;
  re_const_arity := arity;
  re_const_gc := false;
  re_const_inl := false;
  re_const_s := s;
|}.

Definition binop (body : string) : remapped_constant :=
  koka_const 2 ("fn(a : int, b : int) { " ++ body ++ " }").

Definition tt_ := "C_t_Corelib_Init_Datatypes_bool_0_true".
Definition ff_ := "C_t_Corelib_Init_Datatypes_bool_1_false".

Definition koka_int_remaps : constant_remappings := [
  (<%% nat %%>, koka_const 0 "int");
  (<%% Nat.add %%>, binop "a + b");
  (<%% Nat.mul %%>, binop "a * b");
  (<%% Nat.sub %%>, binop "if a < b then 0 else a - b");
  (<%% Nat.max %%>, binop "if a < b then b else a");
  (<%% Nat.min %%>, binop "if a < b then a else b");
  (<%% Nat.div %%>, binop "if b == 0 then 0 else a / b");
  (<%% Nat.modulo %%>, binop "if b == 0 then a else a % b");
  (<%% Nat.pow %%>, binop "pow(a, b)");
  (<%% Nat.eqb %%>, binop ("if a == b then " ++ tt_ ++ " else " ++ ff_));
  (<%% Nat.leb %%>, binop ("if a <= b then " ++ tt_ ++ " else " ++ ff_));
  (<%% Nat.ltb %%>, binop ("if a < b then " ++ tt_ ++ " else " ++ ff_));
  (<%% Nat.compare %%>, binop ("if a < b then C_t_Corelib_Init_Datatypes_comparison_1_Lt else if a == b then C_t_Corelib_Init_Datatypes_comparison_0_Eq else C_t_Corelib_Init_Datatypes_comparison_2_Gt"))
].
