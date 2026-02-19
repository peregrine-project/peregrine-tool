
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Bool.DecBool.
Require Import Stdlib.Arith.Arith.


Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

#[global] Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.
#[global] Instance AsciiEq: Eq ascii := { eq_dec:= ascii_dec }.
#[global] Instance StringEq: Eq string := { eq_dec:= string_dec }.
