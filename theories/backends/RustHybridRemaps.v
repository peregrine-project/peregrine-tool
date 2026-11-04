(** The HYBRID numeric representation of the Rust backend: one representation
    with a fast path, as Lean's [Nat] and OCaml's Zarith have.

    A number is a [Num<'a>], one tagged 64-bit word as in OCaml: an odd word
    [2v+1] holds a small value [v] in [-2^62, 2^62), and an even word is the
    address of an arena-allocated [rug::Integer] holding any other value.  The
    representation is canonical: a value in the small range is always small.
    [Num] is [Copy] and 8 bytes, the size of an [i64], so it fits the backend's
    [<A: Copy>] discipline and a constructor field holding a number is as large
    as in [rust-i64].  [Num::S(v)] builds a small number from a [v] known to be
    in range (literals, a predecessor, a halving); [__int] range-checks.

    Every operation computes on the tagged words when its arguments are small:
    addition and subtraction add [2y] to [2x+1], multiplication multiplies
    [2x] by [y], each with [checked_*] arithmetic, whose overflow is exactly
    the overflow of the small range.  On overflow, or when an argument is big,
    it computes with GMP on references to the arguments (a small argument is
    converted into a stack temporary) and normalizes the result.  So, unlike
    [rust-i64] (which wraps around silently) and [rust-mixed] (which panics on a
    big argument and allocates a GMP integer for every result), the result is
    always the exact one, and a small result allocates nothing.

    Memory: the arena frees nothing before the program ends, and it does not run
    destructors, so the limbs of a big number live as long as the arena.  GMP
    temporaries are owned values and are freed when the operation returns.
    Eliminators are [macro_rules!] (no [self]); a big predecessor is
    [Box::leak]ed, as in [RustGMPRemaps.v], and a small one is a plain value.
    [RustHybridCoherence.v] proves, for a model over [Z], that the fast paths,
    floor division, the comparisons, the eliminators and every entry of the
    remap table compute what the Rocq functions compute; that the Rust strings
    implement the model is trusted.  The only [unsafe] code dereferences an
    even word, and the private field of [Num] in [mod __hybrid] makes
    [of_big] the only source of even words.
    Cargo dependencies: [rug = "1"], [bumpalo = "3"]. *)

From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import RustBackend.
From Peregrine Require Import RustGMPRemaps.
From TypedExtraction Require Import Common.

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
    "Int<'a>" ["self.__nat_zero()"; "self.__nat_succ"] (Some "__nat_elim!");
  ind_remap {| inductive_mind := <%% positive %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__pos_onebit"; "self.__pos_zerobit"; "self.__pos_one()"]
    (Some "__pos_elim!");
  ind_remap {| inductive_mind := <%% N %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__N_zero()"; "self.__N_frompos"] (Some "__N_elim!");
  ind_remap {| inductive_mind := <%% Z %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__Z_zero()"; "self.__Z_frompos"; "self.__Z_fromneg"]
    (Some "__Z_elim!")
].

(** A remap whose body calls the program-preamble method [m] on the arguments. *)
Definition un (m : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self." ++ m ++ "(a) }").
Definition bin (m : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> Int<'a> { self." ++ m ++ "(a, b) }").
Definition binv (body : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> Int<'a> { " ++ body ++ " }").
Definition bpred (body : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> bool { " ++ body ++ " }").
Definition cmp : remapped_constant :=
  mk_const "fn ##name##(&'a self, a: Int<'a>, b: Int<'a>) -> std::cmp::Ordering { a.cmp(&b) }".
Definition same : remapped_constant :=
  mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { a }".

Definition min_ := binv "if a <= b { a } else { b }".
Definition max_ := binv "if a >= b { a } else { b }".
(** [max(x, lo)] *)
Definition clamp (e lo : string) : string := "{ let r = " ++ e ++ "; if r < Num::S(" ++ lo ++ ") { Num::S(" ++ lo ++ ") } else { r } }".

Definition hybrid_const_remaps : constant_remappings := [
  (* --- positive --- *)
  (<%% Pos.add %%>, bin "__add");
  (<%% Pos.succ %%>, mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self.__add(a, Num::S(1)) }");
  (<%% Pos.pred %%>, mk_const ("fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { " ++ clamp "self.__sub(a, Num::S(1))" "1" ++ " }"));
  (<%% Pos.sub %%>, binv (clamp "self.__sub(a, b)" "1"));
  (<%% Pos.mul %%>, bin "__mul");
  (<%% Pos.min %%>, min_);
  (<%% Pos.max %%>, max_);
  (<%% Pos.eqb %%>, bpred "a == b");
  (<%% Pos.compare %%>, cmp);

  (* --- N --- *)
  (<%% N.add %%>, bin "__add");
  (<%% N.succ %%>, mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self.__add(a, Num::S(1)) }");
  (<%% N.pred %%>, mk_const ("fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { " ++ clamp "self.__sub(a, Num::S(1))" "0" ++ " }"));
  (<%% N.sub %%>, binv (clamp "self.__sub(a, b)" "0"));
  (<%% N.mul %%>, bin "__mul");
  (<%% N.div %%>, bin "__divf");
  (<%% N.modulo %%>, bin "__modf");
  (<%% N.min %%>, min_);
  (<%% N.max %%>, max_);
  (<%% N.eqb %%>, bpred "a == b");
  (<%% N.compare %%>, cmp);

  (* --- Z --- *)
  (<%% Z.add %%>, bin "__add");
  (<%% Z.succ %%>, mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self.__add(a, Num::S(1)) }");
  (<%% Z.pred %%>, mk_const "fn ##name##(&'a self, a: Int<'a>) -> Int<'a> { self.__sub(a, Num::S(1)) }");
  (<%% Z.sub %%>, bin "__sub");
  (<%% Z.mul %%>, bin "__mul");
  (<%% Z.opp %%>, un "__neg");
  (<%% Z.min %%>, min_);
  (<%% Z.max %%>, max_);
  (<%% Z.eqb %%>, bpred "a == b");
  (<%% Z.div %%>, bin "__divf");
  (<%% Z.modulo %%>, bin "__modf");
  (<%% Z.compare %%>, cmp);
  (<%% Z.of_N %%>, same);
  (<%% Z.abs_N %%>, un "__abs");

  (* --- nat --- *)
  (<%% Nat.add %%>, bin "__add");
  (<%% Nat.mul %%>, bin "__mul");
  (<%% Nat.sub %%>, binv (clamp "self.__sub(a, b)" "0"));
  (<%% Nat.eqb %%>, bpred "a == b");
  (<%% Nat.leb %%>, bpred "a <= b");
  (<%% Nat.ltb %%>, bpred "a < b");
  (<%% Nat.compare %%>, cmp);
  (<%% Nat.max %%>, max_);
  (<%% Nat.min %%>, min_);
  (<%% Nat.div %%>, bin "__divf");
  (<%% Nat.modulo %%>, bin "__modf");
  (<%% Nat.pow %%>, bin "__pow")
].

(** Outside [impl<'a> Program]: the [Num] type, its comparisons and the
    eliminators.  [__big] converts to an owned GMP integer, [__bref] to a
    reference (a small value is assigned to the caller's temporary), and
    [__leak] builds the canonical [Num] of a GMP integer outside the arena (for
    the eliminators).  [__gmp1]/[__gmp2] bind GMP references to the arguments
    for the slow path.  Comparisons use canonicity: a small and a big number
    differ, and the big one is beyond the small range on the side of its sign. *)
Definition hybrid_top_preamble : string :=
  String.concat MRString.nl [
  "use rug::Integer;";
  "use rug::Assign;";
  "use rug::ops::{DivRounding, RemRounding, Pow};";
  "mod __hybrid {";
  "  // The only code that reads or builds the word of a Num.  Invariant: an odd";
  "  // word is 2v+1 for a small v; an even word is the address of a rug::Integer";
  "  // that lives for 'a (of_big takes a &'a reference; Integer is 8-aligned).";
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
  "    #[inline(always)] pub fn of_big(b: &'a rug::Integer) -> Num<'a> { Num(b as *const rug::Integer as usize as i64, std::marker::PhantomData) }";
  "    #[inline(always)] pub fn small(self) -> Option<i64> { if self.0 & 1 == 1 { Some(self.0 >> 1) } else { None } }";
  "    #[inline(always)] pub fn view(self) -> View<'a> { if self.0 & 1 == 1 { View::S(self.0 >> 1) } else { View::B(unsafe { &*(self.0 as usize as *const rug::Integer) }) } }";
  "    /// Fast paths on two small numbers: None when an argument is big or the result leaves the small range.";
  "    #[inline(always)] pub fn add_small(a: Num<'a>, b: Num<'a>) -> Option<Num<'a>> { if a.0 & b.0 & 1 == 1 { a.0.checked_add(b.0 - 1).map(|r| Num(r, std::marker::PhantomData)) } else { None } }";
  "    #[inline(always)] pub fn sub_small(a: Num<'a>, b: Num<'a>) -> Option<Num<'a>> { if a.0 & b.0 & 1 == 1 { a.0.checked_sub(b.0 - 1).map(|r| Num(r, std::marker::PhantomData)) } else { None } }";
  "    #[inline(always)] pub fn mul_small(a: Num<'a>, b: Num<'a>) -> Option<Num<'a>> { if a.0 & b.0 & 1 == 1 { (a.0 - 1).checked_mul(b.0 >> 1).map(|r| Num(r + 1, std::marker::PhantomData)) } else { None } }";
  "  }";
  "}";
  "use __hybrid::{Num, View};";
  "type Int<'a> = Num<'a>;";
  "const __SMIN: i64 = __hybrid::SMIN;";
  "const __SMAX: i64 = __hybrid::SMAX;";
  "#[inline(always)] fn __fits(v: i64) -> bool { v >= __SMIN && v <= __SMAX }";
  "fn __big(x: Num) -> rug::Integer { match x.view() { View::S(v) => rug::Integer::from(v), View::B(b) => b.clone() } }";
  "fn __bref<'t>(x: Num<'t>, tmp: &'t mut rug::Integer) -> &'t rug::Integer { match x.view() { View::S(v) => { tmp.assign(v); tmp } View::B(b) => b } }";
  "fn __leak(x: rug::Integer) -> Num<'static> { match x.to_i64() { Some(v) if __fits(v) => Num::S(v), _ => Num::of_big(Box::leak(Box::new(x))) } }";
  "fn __leak_i64(v: i64) -> Num<'static> { if __fits(v) { Num::S(v) } else { __leak(rug::Integer::from(v)) } }";
  "impl<'a> PartialEq for Num<'a> { fn eq(&self, o: &Self) -> bool { match (self.view(), o.view()) { (View::S(a), View::S(b)) => a == b, (View::B(a), View::B(b)) => a == b, _ => false } } }";
  "impl<'a> Eq for Num<'a> {}";
  "impl<'a> Ord for Num<'a> { fn cmp(&self, o: &Self) -> std::cmp::Ordering { match (self.view(), o.view()) { (View::S(a), View::S(b)) => a.cmp(&b), (View::S(_), View::B(b)) => b.cmp0().reverse(), (View::B(a), View::S(_)) => a.cmp0(), (View::B(a), View::B(b)) => a.cmp(b) } } }";
  "impl<'a> PartialOrd for Num<'a> { fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) } }";
  "impl<'a> std::fmt::Display for Num<'a> { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { match self.view() { View::S(v) => write!(f, ""{}"", v), View::B(b) => write!(f, ""{}"", b) } } }";
  "impl<'a> std::fmt::Debug for Num<'a> { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { std::fmt::Display::fmt(self, f) } }";
  "macro_rules! __gmp1 { ($a:expr, |$x:ident| $e:expr) => { { let mut __t1 = rug::Integer::new(); let $x = __bref($a, &mut __t1); $e } } }";
  "macro_rules! __gmp2 { ($a:expr, $b:expr, |$x:ident, $y:ident| $e:expr) => { { let (mut __t1, mut __t2) = (rug::Integer::new(), rug::Integer::new()); let $x = __bref($a, &mut __t1); let $y = __bref($b, &mut __t2); $e } } }";
  "";
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "macro_rules! __bool_elim { ($tcase:expr, $fcase:expr, $val:expr) => { if $val { $tcase } else { $fcase } } }";
  cmp_elim_macro;
  "";
  "macro_rules! __nat_elim {";
  "  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "    { let v: Num = $val;";
  "      match v.view() { View::S(0) => $zcase,";
  "        View::S(n) => { let $pred: Num = Num::S(n - 1); $scase },";
  "        View::B(b) => { let $pred: Num = __leak(rug::Integer::from(b - 1u32)); $scase } } }";
  "  }";
  "}";
  "";
  "macro_rules! __pos_elim {";
  "  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "    { let v: Num = $val;";
  "      match v.view() { View::S(1) => $onecase,";
  "        View::S(n) => if n & 1 == 1 { let $p: Num = Num::S(n >> 1); $onebcase } else { let $p2: Num = Num::S(n >> 1); $zerobcase },";
  "        View::B(b) => { if b.is_odd() { let $p: Num = __leak(rug::Integer::from(b >> 1u32)); $onebcase } else { let $p2: Num = __leak(rug::Integer::from(b >> 1u32)); $zerobcase } } } }";
  "  }";
  "}";
  "";
  "macro_rules! __N_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
  "    { let $p: Num = $val; if $p == Num::S(0) { $zero_case } else { $pos_case } }";
  "  }";
  "}";
  "";
  "macro_rules! __Z_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
  "    { let n: Num = $val;";
  "      if n == Num::S(0) { $zero_case }";
  "      else if n < Num::S(0) { let $p2: Num = match n.view() { View::S(v) => __leak_i64(-v), View::B(b) => __leak(rug::Integer::from(-b)) }; $neg_case }";
  "      else { let $p: Num = n; $pos_case } }";
  "  }";
  "}"
  ].

(** Inside [impl<'a> Program]: the constructors and the arithmetic.  [__int]
    and [__num] build the canonical [Num] of an [i64] and of a GMP integer, in
    the arena.  [__divf] and [__modf] are floor division and its remainder
    (Rocq's [Z.div] and [Z.modulo]; on naturals they are the truncating ones),
    with [x / 0 = 0] and [x mod 0 = x]. *)
Definition hybrid_program_preamble : string :=
  String.concat MRString.nl [
  "fn __int(&'a self, v: i64) -> Num<'a> { if __fits(v) { Num::S(v) } else { Num::of_big(self.alloc(rug::Integer::from(v))) } }";
  "fn __num(&'a self, x: rug::Integer) -> Num<'a> { match x.to_i64() { Some(v) if __fits(v) => Num::S(v), _ => Num::of_big(self.alloc(x)) } }";
  "fn __add(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let Some(r) = Num::add_small(a, b) { return r } self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x + y))) }";
  "fn __sub(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let Some(r) = Num::sub_small(a, b) { return r } self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x - y))) }";
  "fn __mul(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let Some(r) = Num::mul_small(a, b) { return r } self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x * y))) }";
  "fn __neg(&'a self, a: Num<'a>) -> Num<'a> { if let Some(x) = a.small() { return self.__int(-x) } self.__num(__gmp1!(a, |x| rug::Integer::from(-x))) }";
  "fn __abs(&'a self, a: Num<'a>) -> Num<'a> { if let Some(x) = a.small() { return self.__int(x.abs()) } self.__num(__gmp1!(a, |x| rug::Integer::from(x.abs_ref()))) }";
  "fn __divf(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  if b == Num::S(0) { return Num::S(0) }";
  "  if let (Some(x), Some(y)) = (a.small(), b.small()) { let (q, r) = (x / y, x % y); return self.__int(if r != 0 && ((r < 0) != (y < 0)) { q - 1 } else { q }) }";
  "  self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x.div_floor(y)))) }";
  "fn __modf(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  if b == Num::S(0) { return a }";
  "  if let (Some(x), Some(y)) = (a.small(), b.small()) { let r = x % y; return Num::S(if r != 0 && ((r < 0) != (y < 0)) { r + y } else { r }) }";
  "  self.__num(__gmp2!(a, b, |x, y| rug::Integer::from(x.rem_floor(y)))) }";
  "fn __pow(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  let e: u32 = match b.small() { Some(v) if v >= 0 && v <= u32::MAX as i64 => v as u32, _ => panic!(""exponent out of range"") };";
  "  if let Some(x) = a.small() { if let Some(r) = x.checked_pow(e) { return self.__int(r) } }";
  "  self.__num(__gmp1!(a, |x| rug::Integer::from(x.pow(e)))) }";
  "fn __nat_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __nat_succ(&'a self, x: Num<'a>) -> Num<'a> { self.__add(x, Num::S(1)) }";
  "fn __pos_one(&'a self) -> Num<'a> { Num::S(1) }";
  "fn __pos_onebit(&'a self, x: Num<'a>) -> Num<'a> { self.__add(self.__mul(x, Num::S(2)), Num::S(1)) }";
  "fn __pos_zerobit(&'a self, x: Num<'a>) -> Num<'a> { self.__mul(x, Num::S(2)) }";
  "fn __N_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __N_frompos(&'a self, z: Num<'a>) -> Num<'a> { z }";
  "fn __Z_zero(&'a self) -> Num<'a> { Num::S(0) }";
  "fn __Z_frompos(&'a self, z: Num<'a>) -> Num<'a> { z }";
  "fn __Z_fromneg(&'a self, z: Num<'a>) -> Num<'a> { self.__neg(z) }"
  ].

Definition hybrid_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some hybrid_top_preamble;
  rust_preamble_program'   := Some hybrid_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
|}.
