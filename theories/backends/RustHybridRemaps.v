(** The HYBRID numeric representation of the Rust backend: one representation
    with a fast path, as Lean's [Nat] and OCaml's Zarith have.

    A number is a [Num<'a>], one tagged 64-bit word as in OCaml: an odd word
    [2v+1] holds a small value [v] in [-2^62, 2^62), and an even word is the
    address of an arena-allocated [rug::Integer] holding any other value.  The
    representation is canonical: a value in the small range is always small.
    [Num] is [Copy] and 8 bytes, the size of an [i64], so it fits the backend's
    [<A: Copy>] discipline and a constructor field holding a number is as large
    as in [rust-i64].

    The arithmetic is written in Rocq ([HybridRuntime.v], over the primitives
    of [HybridPrims.v]) and printed by the typed Rust printer into
    [HybridRuntimeGen.v] ([scripts/gen-hybrid-runtime.py]); this file puts
    those methods into every program and sends the [nat], [positive], [N] and
    [Z] operations to them.  [HybridRuntime.v] proves that each operation
    computes the integer operation, that the fast paths stay in range and
    build only canonical numbers, and that each function of the table agrees
    with the Rocq function it replaces.  Trusted: the one line of Rust bound to
    each primitive ([scripts/HybridRuntimeExtract.v]), the kernel
    [mod __hybrid] below with its comparisons (modelled in
    [RustHybridCoherence.v]), the one-line eliminator macros, rug and GMP.  The only [unsafe] code
    dereferences an even word; even words come only from [of_integer], which
    builds one only for a value outside the small range, and [of_odd_word]
    receives only odd words ([HybridRuntime.add_fast_ok] and the others).

    Memory: the arena frees nothing before the program ends, and it does not run
    destructors, so the limbs of a big number live as long as the arena.  GMP
    temporaries are owned values and are freed when the operation returns.
    The eliminators are [macro_rules!] that match on the views of
    [HybridRuntime.v] ([nat_view] and the others, proved in [nat_view_ok] ...);
    a macro body cannot name [self], so their remaps print
    [__nat_elim!(self, ...)], which the typed Rust printer supports for an
    eliminator ending with a comma.
    Cargo dependencies: [rug = "1"], [bumpalo = "3"]. *)

From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import RustBackend.
From Peregrine Require Import RustGMPRemaps.
From TypedExtraction Require Import Common.
From TypedExtraction Require RustExtract.
From Peregrine Require HybridPrims HybridRuntime.
From Peregrine Require Import HybridRuntimeGen.

From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import PArith.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope bs_scope.

Definition hybrid_ind_remaps : inductive_remappings := [
  ind_remap {| inductive_mind := <%% bool %%>; inductive_ind := 0 |}
    "bool" ["true"; "false"] (Some "__bool_elim!");
  comparison_ind_remap;
  ind_remap {| inductive_mind := <%% nat %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__nat_zero()"; "self.__nat_succ"] (Some "__nat_elim!(self,");
  ind_remap {| inductive_mind := <%% positive %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__pos_onebit"; "self.__pos_zerobit"; "self.__pos_one()"]
    (Some "__pos_elim!(self,");
  ind_remap {| inductive_mind := <%% N %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__N_zero()"; "self.__N_frompos"] (Some "__N_elim!(self,");
  ind_remap {| inductive_mind := <%% Z %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__Z_zero()"; "self.__Z_frompos"; "self.__Z_fromneg"]
    (Some "__Z_elim!(self,")
].

(** The name the printer gives to the Rocq constant [kn] (full names). *)
Definition rt (kn : kername) : string := RustExtract.clean_global_ident (string_of_kername kn).

(** A remap that calls the runtime function [kn] on the arguments. *)
Definition call1 (kn : kername) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self." ++ rt kn ++ "(a) }").
Definition call2 (kn : kername) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> Int<'a> { self." ++ rt kn ++ "(a, b) }").
Definition pred2 (kn : kername) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> bool { self." ++ rt kn ++ "(a, b) }").
Definition cmp2 (kn : kername) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> std::cmp::Ordering { self." ++ rt kn ++ "(a, b) }").
Definition same : remapped_constant :=
  mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { a }".

(** Each entry sends a Rocq function to the runtime function that the lemma
    of the same name in [HybridRuntime.v] ([nat_add_ok], [pos_pred_ok], ...)
    proves equal to it. *)
Definition hybrid_const_remaps : constant_remappings := [
  (* --- positive --- *)
  (<%% Pos.add %%>, call2 <%% HybridRuntime.add %%>);
  (<%% Pos.succ %%>, call1 <%% HybridRuntime.succ %%>);
  (<%% Pos.pred %%>, call1 <%% HybridRuntime.pred1 %%>);
  (<%% Pos.sub %%>, call2 <%% HybridRuntime.sub1 %%>);
  (<%% Pos.mul %%>, call2 <%% HybridRuntime.mul %%>);
  (<%% Pos.min %%>, call2 <%% HybridRuntime.min %%>);
  (<%% Pos.max %%>, call2 <%% HybridRuntime.max %%>);
  (<%% Pos.eqb %%>, pred2 <%% HybridPrims.num_eqb %%>);
  (<%% Pos.compare %%>, cmp2 <%% HybridPrims.num_compare %%>);

  (* --- N --- *)
  (<%% N.add %%>, call2 <%% HybridRuntime.add %%>);
  (<%% N.succ %%>, call1 <%% HybridRuntime.succ %%>);
  (<%% N.pred %%>, call1 <%% HybridRuntime.pred0 %%>);
  (<%% N.sub %%>, call2 <%% HybridRuntime.sub0 %%>);
  (<%% N.mul %%>, call2 <%% HybridRuntime.mul %%>);
  (<%% N.div %%>, call2 <%% HybridRuntime.divf %%>);
  (<%% N.modulo %%>, call2 <%% HybridRuntime.modf %%>);
  (<%% N.min %%>, call2 <%% HybridRuntime.min %%>);
  (<%% N.max %%>, call2 <%% HybridRuntime.max %%>);
  (<%% N.eqb %%>, pred2 <%% HybridPrims.num_eqb %%>);
  (<%% N.compare %%>, cmp2 <%% HybridPrims.num_compare %%>);

  (* --- Z --- *)
  (<%% Z.add %%>, call2 <%% HybridRuntime.add %%>);
  (<%% Z.succ %%>, call1 <%% HybridRuntime.succ %%>);
  (<%% Z.pred %%>, call1 <%% HybridRuntime.pred %%>);
  (<%% Z.sub %%>, call2 <%% HybridRuntime.sub %%>);
  (<%% Z.mul %%>, call2 <%% HybridRuntime.mul %%>);
  (<%% Z.opp %%>, call1 <%% HybridRuntime.neg %%>);
  (<%% Z.min %%>, call2 <%% HybridRuntime.min %%>);
  (<%% Z.max %%>, call2 <%% HybridRuntime.max %%>);
  (<%% Z.eqb %%>, pred2 <%% HybridPrims.num_eqb %%>);
  (<%% Z.div %%>, call2 <%% HybridRuntime.divf %%>);
  (<%% Z.modulo %%>, call2 <%% HybridRuntime.modf %%>);
  (<%% Z.compare %%>, cmp2 <%% HybridPrims.num_compare %%>);
  (<%% Z.of_N %%>, same);
  (<%% Z.abs_N %%>, call1 <%% HybridRuntime.abs %%>);

  (* --- nat --- *)
  (<%% Nat.add %%>, call2 <%% HybridRuntime.add %%>);
  (<%% Nat.mul %%>, call2 <%% HybridRuntime.mul %%>);
  (<%% Nat.sub %%>, call2 <%% HybridRuntime.sub0 %%>);
  (<%% Nat.eqb %%>, pred2 <%% HybridPrims.num_eqb %%>);
  (<%% Nat.leb %%>, pred2 <%% HybridRuntime.leb %%>);
  (<%% Nat.ltb %%>, pred2 <%% HybridRuntime.ltb %%>);
  (<%% Nat.compare %%>, cmp2 <%% HybridPrims.num_compare %%>);
  (<%% Nat.max %%>, call2 <%% HybridRuntime.max %%>);
  (<%% Nat.min %%>, call2 <%% HybridRuntime.min %%>);
  (<%% Nat.div %%>, call2 <%% HybridRuntime.divf %%>);
  (<%% Nat.modulo %%>, call2 <%% HybridRuntime.modf %%>);
  (<%% Nat.pow %%>, call2 <%% HybridRuntime.pow %%>)
].

(** Outside [impl<'a> Program]: the [Num] type, its comparisons, the view
    enums and the eliminators.  [__big] converts to an owned GMP integer,
    [__bref] to a reference (a small value is assigned to the caller's
    temporary).  [__gmp1]/[__gmp2] bind GMP references to the arguments for
    the slow path.  Comparisons use canonicity: a small and a big number
    differ, and the big one is beyond the small range on the side of its sign. *)
Definition hybrid_top_preamble : string :=
  String.concat MRString.nl [
  "use rug::Integer;";
  "use rug::Assign;";
  "use rug::ops::{DivRounding, RemRounding, Pow};";
  "mod __hybrid {";
  "  // The only code that reads or builds the word of a Num.  Invariant: an odd";
  "  // word is 2v+1 for a small v; an even word is the address of a rug::Integer";
  "  // that lives for 'a (of_big takes a &'a reference; Integer is 8-aligned) and";
  "  // whose value is outside the small range (of_integer, the only caller, checks).";
  "  // The field is private, so no other code can build an even word, and";
  "  // view() dereferences only even words.";
  "  #[derive(Clone, Copy)]";
  "  pub struct Num<'a>(i64, std::marker::PhantomData<&'a rug::Integer>);";
  "  pub enum View<'a> { S(i64), B(&'a rug::Integer) }";
  "  pub const SMIN: i64 = -(1i64 << 62);";
  "  pub const SMAX: i64 = (1i64 << 62) - 1;";
  "  impl<'a> Num<'a> {";
  "    /// A small number; v must be in [SMIN, SMAX] (out of range gives a wrong small value, never an invalid address).";
  "    #[inline(always)] pub const fn S(v: i64) -> Num<'a> { Num(v.wrapping_shl(1) | 1, std::marker::PhantomData) }";
  "    #[inline(always)] fn of_big(b: &'a rug::Integer) -> Num<'a> { Num(b as *const rug::Integer as usize as i64, std::marker::PhantomData) }";
  "    /// The number b: small when b is in [SMIN, SMAX], so the representation stays canonical.";
  "    #[inline(always)] pub fn of_integer(b: &'a rug::Integer) -> Num<'a> { match b.to_i64() { Some(v) if v >= SMIN && v <= SMAX => Num::S(v), _ => Num::of_big(b) } }";
  "    #[inline(always)] pub fn small(self) -> Option<i64> { if self.0 & 1 == 1 { Some(self.0 >> 1) } else { None } }";
  "    #[inline(always)] pub fn view(self) -> View<'a> { if self.0 & 1 == 1 { View::S(self.0 >> 1) } else { View::B(unsafe { &*(self.0 as usize as *const rug::Integer) }) } }";
  "    /// Fast paths on two small numbers: None when an argument is big or the result leaves the small range.";
  "    #[inline(always)] pub fn word(self) -> i64 { self.0 }";
  "    #[inline(always)] pub fn both_small(a: Num<'a>, b: Num<'a>) -> bool { a.0 & b.0 & 1 == 1 }";
  "    /// The small number w >> 1 of an odd word w; HybridRuntime.v proves that every call passes an odd word.";
  "    #[inline(always)] pub fn of_odd_word(w: i64) -> Num<'a> { debug_assert!(w & 1 == 1); Num(w, std::marker::PhantomData) }";
  "  }";
  "}";
  "use __hybrid::{Num, View};";
  "type Int<'a> = Num<'a>;";
  "const __SMIN: i64 = __hybrid::SMIN;";
  "const __SMAX: i64 = __hybrid::SMAX;";
  "#[inline(always)] fn __fits(v: i64) -> bool { v >= __SMIN && v <= __SMAX }";
  "fn __big(x: Num) -> rug::Integer { match x.view() { View::S(v) => rug::Integer::from(v), View::B(b) => b.clone() } }";
  "fn __bref<'t>(x: Num<'t>, tmp: &'t mut rug::Integer) -> &'t rug::Integer { match x.view() { View::S(v) => { tmp.assign(v); tmp } View::B(b) => b } }";
  "impl<'a> PartialEq for Num<'a> { fn eq(&self, o: &Self) -> bool { match (self.view(), o.view()) { (View::S(a), View::S(b)) => a == b, (View::B(a), View::B(b)) => a == b, _ => false } } }";
  "impl<'a> Eq for Num<'a> {}";
  "impl<'a> Ord for Num<'a> { fn cmp(&self, o: &Self) -> std::cmp::Ordering { match (self.view(), o.view()) { (View::S(a), View::S(b)) => a.cmp(&b), (View::S(_), View::B(b)) => b.cmp0().reverse(), (View::B(a), View::S(_)) => a.cmp0(), (View::B(a), View::B(b)) => a.cmp(b) } } }";
  "impl<'a> PartialOrd for Num<'a> { fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) } }";
  "impl<'a> std::fmt::Display for Num<'a> { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { match self.view() { View::S(v) => write!(f, ""{}"", v), View::B(b) => write!(f, ""{}"", b) } } }";
  "impl<'a> std::fmt::Debug for Num<'a> { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { std::fmt::Display::fmt(self, f) } }";
  "macro_rules! __gmp1 { ($a:expr, |$x:ident| $e:expr) => { { let mut __t1 = rug::Integer::new(); let $x = __bref($a, &mut __t1); $e } } }";
  "macro_rules! __gmp2 { ($a:expr, $b:expr, |$x:ident, $y:ident| $e:expr) => { { let (mut __t1, mut __t2) = (rug::Integer::new(), rug::Integer::new()); let $x = __bref($a, &mut __t1); let $y = __bref($b, &mut __t2); $e } } }";
  "";
  "macro_rules! __opt_elim { ($w:ident, $some:expr, $none:expr, $val:expr) => { match $val { Some($w) => $some, None => $none } } }";
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "macro_rules! __bool_elim { ($tcase:expr, $fcase:expr, $val:expr) => { if $val { $tcase } else { $fcase } } }";
  cmp_elim_macro;
  "";
  "#[derive(Clone, Copy)] enum PosView<'a> { I(Num<'a>), O(Num<'a>), H }";
  "#[derive(Clone, Copy)] enum ZView<'a> { Z, P(Num<'a>), N(Num<'a>) }";
  "";
  "// The eliminators take self (their remaps print __nat_elim!(self, ...)) and";
  "// match on the views of HybridRuntime.v.";
  "macro_rules! __nat_elim { ($s:expr, $zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "  match $s." ++ rt <%% HybridRuntime.nat_view %%> ++ "($val) { None => $zcase, Some($pred) => $scase } } }";
  "macro_rules! __pos_elim { ($s:expr, $p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "  match $s." ++ rt <%% HybridRuntime.pos_view %%> ++ "($val) { PosView::I($p) => $onebcase, PosView::O($p2) => $zerobcase, PosView::H => $onecase } } }";
  "macro_rules! __N_elim { ($s:expr, $zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
  "  match $s." ++ rt <%% HybridRuntime.N_view %%> ++ "($val) { None => $zero_case, Some($p) => $pos_case } } }";
  "macro_rules! __Z_elim { ($s:expr, $zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
  "  match $s." ++ rt <%% HybridRuntime.Z_view %%> ++ "($val) { ZView::Z => $zero_case, ZView::P($p) => $pos_case, ZView::N($p2) => $neg_case } } }"
  ].

(** Inside [impl<'a> Program]: [__int] and [__num], the canonical [Num] of
    an [i64] and of a GMP integer in the arena (used by the primitives), the
    constructor methods of the inductive remaps, and the runtime. *)
Definition hybrid_program_preamble : string :=
  String.concat MRString.nl (List.app [
  "fn __int(&'a self, v: i64) -> Num<'a> { if __fits(v) { Num::S(v) } else { Num::of_integer(self.alloc(rug::Integer::from(v))) } }";
  "fn __num(&'a self, x: rug::Integer) -> Num<'a> { match x.to_i64() { Some(v) if __fits(v) => Num::S(v), _ => Num::of_integer(self.alloc(x)) } }";
  "fn __nat_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __nat_succ(&'a self, x: Num<'a>) -> Num<'a> { self." ++ rt <%% HybridRuntime.succ %%> ++ "(x) }";
  "fn __pos_one(&'a self) -> Num<'a> { Num::S(1) }";
  "fn __pos_onebit(&'a self, x: Num<'a>) -> Num<'a> { self." ++ rt <%% HybridRuntime.double_plus_one %%> ++ "(x) }";
  "fn __pos_zerobit(&'a self, x: Num<'a>) -> Num<'a> { self." ++ rt <%% HybridRuntime.double %%> ++ "(x) }";
  "fn __N_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __N_frompos(&'a self, z: Num<'a>) -> Num<'a> { z }";
  "fn __Z_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __Z_frompos(&'a self, z: Num<'a>) -> Num<'a> { z }";
  "fn __Z_fromneg(&'a self, z: Num<'a>) -> Num<'a> { self." ++ rt <%% HybridRuntime.neg %%> ++ "(z) }"
  ] hybrid_runtime_lines).

Definition hybrid_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some hybrid_top_preamble;
  rust_preamble_program'   := Some hybrid_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
|}.
