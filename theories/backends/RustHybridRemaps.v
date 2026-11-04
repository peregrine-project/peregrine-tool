(** The HYBRID numeric representation of the Rust backend: one representation
    with a fast path, as Lean's [Nat] and OCaml's Zarith have.

    A number is a [Num<'a>]: [Num::S(v)] holds a value that fits in [i64], and
    [Num::B(b)] holds any other value as an arena-allocated [&'a rug::Integer].
    The representation is canonical: a value that fits in [i64] is always
    [Num::S].  [Num] is [Copy], so it fits the backend's [<A: Copy>] discipline
    without an arena allocation for small values.

    Every operation computes on [i64] when its arguments are small, with
    [checked_*] arithmetic; on overflow, or when an argument is big, it computes
    with GMP and normalizes the result back to [Num::S] when it fits.  So, unlike
    [rust-i64] (which wraps around silently) and [rust-mixed] (which panics on a
    big argument and allocates a GMP integer for every result), the result is
    always the exact one, and a small result allocates nothing.

    Eliminators are [macro_rules!] (no [self]); a big predecessor is
    [Box::leak]ed, as in [RustGMPRemaps.v], and a small one is a plain value.
    Nothing about the remapped operations is verified.
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
    eliminators.  [__big] converts to a GMP integer, [__leak] builds the
    canonical [Num] of a GMP integer outside the arena (for the eliminators). *)
Definition hybrid_top_preamble : string :=
  String.concat MRString.nl [
  "use rug::Integer;";
  "use rug::ops::{DivRounding, RemRounding, Pow};";
  "#[derive(Debug, Clone, Copy)]";
  "pub enum Num<'a> { S(i64), B(&'a rug::Integer) }";
  "type Int<'a> = Num<'a>;";
  "fn __big(x: Num) -> rug::Integer { match x { Num::S(v) => rug::Integer::from(v), Num::B(b) => b.clone() } }";
  "fn __leak(x: rug::Integer) -> Num<'static> { match x.to_i64() { Some(v) => Num::S(v), None => Num::B(Box::leak(Box::new(x))) } }";
  "impl<'a> PartialEq for Num<'a> { fn eq(&self, o: &Self) -> bool { match (self, o) { (Num::S(a), Num::S(b)) => a == b, (Num::S(_), Num::B(_)) | (Num::B(_), Num::S(_)) => false, (Num::B(a), Num::B(b)) => a == b } } }";
  "impl<'a> Eq for Num<'a> {}";
  "impl<'a> Ord for Num<'a> { fn cmp(&self, o: &Self) -> std::cmp::Ordering { match (self, o) { (Num::S(a), Num::S(b)) => a.cmp(b), _ => __big(*self).cmp(&__big(*o)) } } }";
  "impl<'a> PartialOrd for Num<'a> { fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) } }";
  "impl<'a> std::fmt::Display for Num<'a> { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { match self { Num::S(v) => write!(f, ""{}"", v), Num::B(b) => write!(f, ""{}"", b) } } }";
  "";
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "macro_rules! __bool_elim { ($tcase:expr, $fcase:expr, $val:expr) => { if $val { $tcase } else { $fcase } } }";
  cmp_elim_macro;
  "";
  "macro_rules! __nat_elim {";
  "  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "    { let v: Num = $val;";
  "      match v { Num::S(0) => $zcase,";
  "        Num::S(n) => { let $pred: Num = Num::S(n - 1); $scase },";
  "        Num::B(b) => { let $pred: Num = __leak(rug::Integer::from(b - 1)); $scase } } }";
  "  }";
  "}";
  "";
  "macro_rules! __pos_elim {";
  "  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "    { let v: Num = $val;";
  "      match v { Num::S(1) => $onecase,";
  "        Num::S(n) => if n & 1 == 1 { let $p: Num = Num::S(n >> 1); $onebcase } else { let $p2: Num = Num::S(n >> 1); $zerobcase },";
  "        Num::B(b) => if b.is_odd() { let $p: Num = __leak(rug::Integer::from(b >> 1u32)); $onebcase } else { let $p2: Num = __leak(rug::Integer::from(b >> 1u32)); $zerobcase } } }";
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
  "      else if n < Num::S(0) { let $p2: Num = match n { Num::S(v) if v != i64::MIN => Num::S(-v), _ => __leak(-__big(n)) }; $neg_case }";
  "      else { let $p: Num = n; $pos_case } }";
  "  }";
  "}"
  ].

(** Inside [impl<'a> Program]: the constructors and the arithmetic.  [__num]
    builds the canonical [Num] of a GMP integer, in the arena.  Each operation
    takes the [i64] path when both arguments are small and the [checked_*]
    operation does not overflow.  [__divf] and [__modf] are floor division and
    its remainder (Rocq's [Z.div] and [Z.modulo]; on naturals they are the
    truncating ones), with [x / 0 = 0] and [x mod 0 = x]. *)
Definition hybrid_program_preamble : string :=
  String.concat MRString.nl [
  "fn __num(&'a self, x: rug::Integer) -> Num<'a> { match x.to_i64() { Some(v) => Num::S(v), None => Num::B(self.alloc(x)) } }";
  "fn __add(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let (Num::S(x), Num::S(y)) = (a, b) { if let Some(r) = x.checked_add(y) { return Num::S(r) } } self.__num(__big(a) + __big(b)) }";
  "fn __sub(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let (Num::S(x), Num::S(y)) = (a, b) { if let Some(r) = x.checked_sub(y) { return Num::S(r) } } self.__num(__big(a) - __big(b)) }";
  "fn __mul(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> { if let (Num::S(x), Num::S(y)) = (a, b) { if let Some(r) = x.checked_mul(y) { return Num::S(r) } } self.__num(__big(a) * __big(b)) }";
  "fn __neg(&'a self, a: Num<'a>) -> Num<'a> { if let Num::S(x) = a { if let Some(r) = x.checked_neg() { return Num::S(r) } } self.__num(-__big(a)) }";
  "fn __abs(&'a self, a: Num<'a>) -> Num<'a> { if let Num::S(x) = a { if let Some(r) = x.checked_abs() { return Num::S(r) } } self.__num(__big(a).abs()) }";
  "fn __divf(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  if b == Num::S(0) { return Num::S(0) }";
  "  if let (Num::S(x), Num::S(y)) = (a, b) { if let (Some(q), Some(r)) = (x.checked_div(y), x.checked_rem(y)) { return Num::S(if r != 0 && ((r < 0) != (y < 0)) { q - 1 } else { q }) } }";
  "  self.__num(__big(a).div_floor(__big(b))) }";
  "fn __modf(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  if b == Num::S(0) { return a }";
  "  if let (Num::S(x), Num::S(y)) = (a, b) { if let Some(r) = x.checked_rem(y) { return Num::S(if r != 0 && ((r < 0) != (y < 0)) { r + y } else { r }) } }";
  "  self.__num(__big(a).rem_floor(__big(b))) }";
  "fn __pow(&'a self, a: Num<'a>, b: Num<'a>) -> Num<'a> {";
  "  let e: u32 = match b { Num::S(v) if v >= 0 && v <= u32::MAX as i64 => v as u32, _ => panic!(""exponent out of range"") };";
  "  if let Num::S(x) = a { if let Some(r) = x.checked_pow(e) { return Num::S(r) } }";
  "  self.__num(__big(a).pow(e)) }";
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
  rust_refcount'           := None;
|}.

(** [rust-rc-hybrid]: the same numbers, with the rest of the program reference
    counted.  A number stays a [Copy] word; a big number is leaked, as the
    eliminators already leak a big predecessor. *)
Definition rc_hybrid_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some hybrid_top_preamble;
  rust_preamble_program'   := Some hybrid_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
  rust_refcount'           := Some true;
|}.
