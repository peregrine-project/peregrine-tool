
(* begin hide *)
From Stdlib Require Import
  List ZArith (* Ascii String *).
From MetaRocq.Utils Require Import bytestring.

From Ceres Require Import
  CeresString
  CeresS.
(* end hide *)

(** Helper for [string_of_sexp]. *)
Local Definition dstring_of_sexp {A} (dstring_A : A -> DString.t)
  : sexp_ A -> DString.t
  := fix _to_dstring (x : sexp_ A) : DString.t :=
    match x with
    | Atom_ a => dstring_A a
    | List nil => "()"%bs
    | List (x :: xs) => fun s0 =>
        (  "("
        :: _to_dstring x
             (fold_right (fun x => " "%byte ++ _to_dstring x)%dstring
                (")" :: s0)
                xs))%bs
    end%dstring.

(** Convert a [sexp] to a [string]. *)
Definition string_of_sexp_ {A} (string_A : A -> string) (x : sexp_ A) : string :=
  dstring_of_sexp string_A x ""%bs.

(** Convert an [atom] to a [string]. *)
Definition string_of_atom (a : atom) : string :=
  match a with
  | Num n => string_of_Z n
  | Str s => escape_string s
  | Raw s => s
  end.

(** Convert a [sexp] to a [string]. *)
Definition string_of_sexp : sexp -> string :=
  string_of_sexp_ string_of_atom.
