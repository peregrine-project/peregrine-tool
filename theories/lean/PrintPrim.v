From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import Show.
From Corelib Require PrimInt63 PrimString PrimStringAxioms.
From Stdlib Require Uint63.
From Stdlib Require Import List.
From Stdlib Require Import Strings.Byte.
From Stdlib Require BinInt BinNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  Primitive literals for the printers of the Lean, F# and Koka      *)
(*  backends.                                                         *)
(* ------------------------------------------------------------------ *)

(* A primitive integer as an unsigned decimal, in [0, 2^63). *)
Definition prim_int_decimal (i : PrimInt63.int) : string := string_of_prim_int i.

Definition hex_digit (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
  | 8 => "8" | 9 => "9" | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d" | 14 => "e" | _ => "f"
  end.

(* One byte of a string literal, in the escape syntax shared by Lean, F# and
   Koka: printable ASCII stands for itself, except the quote and the
   backslash; every other byte becomes [\xHH].  A byte from [0x80] on is
   then the character [U+00HH], so a literal with non-ASCII bytes denotes a
   different string in the target. *)
Definition escape_byte (b : byte) : string :=
  let n := Byte.to_nat b in
  if Nat.eqb n 34 then "\"""
  else if Nat.eqb n 92 then "\\"
  else if Nat.eqb n 10 then "\n"
  else if andb (Nat.leb 32 n) (Nat.leb n 126) then String.String b String.EmptyString
  else "\x" ++ hex_digit (Nat.div n 16) ++ hex_digit (Nat.modulo n 16).

Definition char63_byte (c : PrimString.char63) : byte :=
  match Byte.of_N (BinInt.Z.to_N (Uint63.to_Z c)) with
  | Some b => b
  | None => Byte.x00
  end.

Definition prim_string_literal (s : PrimString.string) : string :=
  """" ++ String.concat "" (List.map (fun c => escape_byte (char63_byte c)) (PrimStringAxioms.to_list s)) ++ """".
