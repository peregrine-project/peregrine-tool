From Stdlib Require Import PrimInt63 PrimString List.
Import ListNotations.

(* Primitive integer and string literals, carried through data and selected
   by a match, so that every backend has to print them. *)
Inductive lit := I (i : int) | Str (s : string).

Definition pick (b : bool) : lit := if b then I 42%uint63 else Str "a""b\c"%pstring.

Definition is_int (l : lit) : nat := match l with I _ => 1 | Str _ => 0 end.

Definition test : list nat := [is_int (pick true); is_int (pick false)].
