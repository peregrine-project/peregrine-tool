(** Prints the [rust-hybrid] number runtime ([HybridRuntime.v]) with the
    typed Rust printer that Peregrine's Rust backend uses, binding each
    primitive of [HybridPrims.v] to its line of Rust.  Run by
    [scripts/gen-hybrid-runtime.py], which writes the printed methods to
    [theories/backends/HybridRuntimeGen.v]; CI checks that the committed
    file is up to date.  The Rust lines below are the trusted part: each
    computes the Rocq body of its primitive. *)

From Stdlib Require Import ZArith List String Bool.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Template Require Import All.
From TypedExtraction Require Import Printing PluginExtract.
From Peregrine Require Import HybridPrims HybridRuntime.
Import ListNotations.
Local Open Scope bs_scope.

Definition P (s : string) : kername := (MPfile ["HybridPrims"; "backends"; "Peregrine"], s).
Definition R (s : string) : kername := (MPfile ["HybridRuntime"; "backends"; "Peregrine"], s).
Definition D (s : string) : kername := (MPfile ["Datatypes"; "Init"; "Corelib"], s).

Definition const_table : list (kername * string) := [
  (P "i_checked_add", "fn ##name##(&'a self, a: i64, b: i64) -> Option<i64> { a.checked_add(b) }");
  (P "i_checked_sub", "fn ##name##(&'a self, a: i64, b: i64) -> Option<i64> { a.checked_sub(b) }");
  (P "i_checked_mul", "fn ##name##(&'a self, a: i64, b: i64) -> Option<i64> { a.checked_mul(b) }");
  (P "i_checked_pow", "fn ##name##(&'a self, x: i64, e: i64) -> Option<i64> { x.checked_pow(e as u32) }");
  (P "i_add", "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }");
  (P "i_sub", "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a - b }");
  (P "i_neg", "fn ##name##(&'a self, a: i64) -> i64 { -a }");
  (P "i_abs", "fn ##name##(&'a self, a: i64) -> i64 { a.abs() }");
  (P "i_shr1", "fn ##name##(&'a self, a: i64) -> i64 { a >> 1 }");
  (P "i_quot", "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a / b }");
  (P "i_rem", "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a % b }");
  (P "i_eqb", "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }");
  (P "i_ltb", "fn ##name##(&'a self, a: i64, b: i64) -> bool { a < b }");
  (P "i_odd", "fn ##name##(&'a self, a: i64) -> bool { a & 1 == 1 }");
  (P "i_0", "fn ##name##(&'a self) -> i64 { 0 }");
  (P "i_1", "fn ##name##(&'a self) -> i64 { 1 }");
  (P "i_2", "fn ##name##(&'a self) -> i64 { 2 }");
  (P "i_u32max", "fn ##name##(&'a self) -> i64 { u32::MAX as i64 }");
  (P "num_small", "fn ##name##(&'a self, a: Num<'a>) -> Option<i64> { a.small() }");
  (P "num_both_small", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> bool { Num::both_small(a, b) }");
  (P "num_word", "fn ##name##(&'a self, a: Num<'a>) -> i64 { a.word() }");
  (P "num_of_word", "fn ##name##(&'a self, w: i64) -> Num<'a> { Num::of_odd_word(w) }");
  (P "num_S", "fn ##name##(&'a self, v: i64) -> Num<'a> { Num::S(v) }");
  (P "num_int", "fn ##name##(&'a self, v: i64) -> Num<'a> { self.__int(v) }");
  (P "num_eqb", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> bool { a == b }");
  (P "num_compare", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> std::cmp::Ordering { a.cmp(&b) }");
  (P "big_add", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x + y))) }");
  (P "big_sub", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x - y))) }");
  (P "big_mul", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x * y))) }");
  (P "big_neg", "fn ##name##(&'a self, a: Num<'a>) -> Num<'a> { self.__num(__gmp1!(a, |x| rug::Integer::from(-x))) }");
  (P "big_abs", "fn ##name##(&'a self, a: Num<'a>) -> Num<'a> { self.__num(__gmp1!(a, |x| rug::Integer::from(x.abs_ref()))) }");
  (P "big_divf", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x.div_floor(y)))) }");
  (P "big_modf", "fn ##name##(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x.rem_floor(y)))) }");
  (P "big_pow", "fn ##name##(&'a self, a: Num<'a>, e: i64) -> Num<'a> { self.__num(__gmp1!(a, |x| rug::Integer::from(x.pow(e as u32)))) }");
  (P "pow_out_of_range", "fn ##name##(&'a self, a: Num<'a>) -> Num<'a> { if a == Num::S(0) || a == Num::S(1) { a } else { panic!(""exponent out of range"") } }")
].

Definition ind_table : list (kername * remapped_inductive) := [
  (D "bool", {| re_ind_name := "bool"; re_ind_ctors := ["true"; "false"]; re_ind_match := Some "__bool_elim!" |});
  (D "comparison", {| re_ind_name := "std::cmp::Ordering"; re_ind_ctors := ["std::cmp::Ordering::Equal"; "std::cmp::Ordering::Less"; "std::cmp::Ordering::Greater"]; re_ind_match := Some "__cmp_elim!" |});
  (P "i64", {| re_ind_name := "i64"; re_ind_ctors := ["__no_I"]; re_ind_match := None |});
  (P "oi64", {| re_ind_name := "Option<i64>"; re_ind_ctors := ["Some"; "None"]; re_ind_match := Some "__opt_elim!" |});
  (P "num", {| re_ind_name := "Num<'a>"; re_ind_ctors := ["__no_Nm"]; re_ind_match := None |});
  (P "onum", {| re_ind_name := "Option<Num<'a>>"; re_ind_ctors := ["Some"; "None"]; re_ind_match := Some "__opt_elim!" |});
  (P "posv", {| re_ind_name := "PosView<'a>"; re_ind_ctors := ["PosView::I"; "PosView::O"; "PosView::H"]; re_ind_match := None |});
  (P "zv", {| re_ind_name := "ZView<'a>"; re_ind_ctors := ["ZView::Z"; "ZView::P"; "ZView::N"]; re_ind_match := None |})
].

Fixpoint lookup {A} (l : list (kername * A)) (kn : kername) : option A :=
  match l with [] => None | (k, a) :: l => if eq_kername k kn then Some a else lookup l kn end.

Definition remaps : remaps := {|
  remap_inductive ind := lookup ind_table (inductive_mind ind);
  remap_constant kn := lookup const_table kn;
  remap_inline_constant _ := None |}.

(** All the functions the remap table calls. *)
Definition entry :=
  (add, sub, mul, neg, abs, divf, modf, pow, leb, ltb, min, max,
   (succ, pred, sub0, sub1, pred0, pred1, double_plus_one, double, id, num_eqb, num_compare),
   (nat_view, N_view, pos_view, Z_view)).

MetaRocq Quote Recursively Definition p := entry.

Definition out := PluginExtract.extract p remaps (fun _ => false).

Eval vm_compute in out.
