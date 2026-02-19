From Stdlib Require Import Extraction.
From Stdlib Require Import ZArith.

Extract Inductive nat => "u64" ["0" "__nat_succ"] "__nat_elim!".
Extract Inductive positive => "u64" ["__pos_onebit" "__pos_zerobit" "1"] "__pos_elim!".
Extract Inductive N => "u64" ["0" "__N_frompos"] "__N_elim!".
Extract Inductive Z => "i64" ["0" "__Z_frompos" "__Z_fromneg"] "__Z_elim!".
Extract Inductive comparison =>
  "std::cmp::Ordering"
    ["std::cmp::Ordering::Equal"
     "std::cmp::Ordering::Less"
     "std::cmp::Ordering::Greater"].

Extract Constant Corelib.BinNums.PosDef.Pos.add => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }".
Extract Constant Corelib.BinNums.PosDef.Pos.succ => "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.pred => "fn ##name##(&'a self, a: u64) -> u64 { a.checked_sub(1).unwrap_or(1) }".
Extract Constant Corelib.BinNums.PosDef.Pos.sub => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_sub(b).unwrap_or(1) }".
Extract Constant Corelib.BinNums.PosDef.Pos.mul => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_mul(b).unwrap() }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.min => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.max => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }".
Extract Constant Corelib.BinNums.PosDef.Pos.eqb => "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }".
Extract Constant Corelib.BinNums.PosDef.Pos.compare =>
"fn ##name##(&'a self, a: u64, b: u64) -> std::cmp::Ordering {
  a.cmp(&b)
}".
Extract Constant Corelib.BinNums.PosDef.Pos.compare_cont =>
"fn ##name##(&'a self, cont: std::cmp::Ordering, a: u64, b: u64) -> std::cmp::Ordering {
  if a < b then
    std::cmp::Ordering::Less
  else if a == b then
    cont
  else
    std::cmp::Ordering::Greater".

Extract Constant Stdlib.NArith.BinNatDef.N.add => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }".
Extract Constant Stdlib.NArith.BinNatDef.N.succ => "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }".
Extract Constant Stdlib.NArith.BinNatDef.N.pred => "fn ##name##(&'a self, a: u64) -> u64 { a.checked_sub(1).unwrap_or(0) }".
Extract Constant Stdlib.NArith.BinNatDef.N.sub => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_sub(b).unwrap_or(0) }".
Extract Constant Stdlib.NArith.BinNatDef.N.mul => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_mul(b).unwrap() }".
Extract Constant Stdlib.NArith.BinNatDef.N.div => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_div(b).unwrap_or(0) }".
Extract Constant Stdlib.NArith.BinNatDef.N.modulo => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_rem(b).unwrap_or(a) }".
Extract Constant Stdlib.NArith.BinNatDef.N.min => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::min(a, b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.max => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { std::cmp::max(a, b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.eqb => "fn ##name##(&'a self, a: u64, b: u64) -> bool { a == b }".
Extract Constant Stdlib.NArith.BinNatDef.N.compare =>
"fn ##name##(&'a self, a: u64, b: u64) -> std::cmp::Ordering { a.cmp(&b) }".

Extract Constant Corelib.BinNums.IntDef.Z.add => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }".
Extract Constant Stdlib.ZArith.BinIntDef.Z.succ => "fn ##name##(&'a self, a: i64) -> i64 { a.checked_add(1).unwrap() }".
Extract Constant Stdlib.ZArith.BinIntDef.Z.pred => "fn ##name##(&'a self, a: i64) -> i64 { a.checked_sub(1).unwrap() }".
Extract Constant Corelib.BinNums.IntDef.Z.sub => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }".
Extract Constant Corelib.BinNums.IntDef.Z.mul => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }".
Extract Constant Corelib.BinNums.IntDef.Z.opp => "fn ##name##(&'a self, a: i64) -> i64 { a.checked_neg().unwrap() }".
Extract Constant Corelib.BinNums.IntDef.Z.min => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::min(a, b) }".
Extract Constant Corelib.BinNums.IntDef.Z.max => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { std::cmp::max(a, b) }".
Extract Constant Corelib.BinNums.IntDef.Z.eqb => "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }".
(* TODO: div and modulo are nontrivial since Rocq rounds towards negative infinity *)
(*Extract ConstanBinIntDef.t Z.div => "fn ##name##(a: i64, b: i64) -> i64 { a.checked_div(b).unwrap_or(0) }".
Extract Constant BinIntDef.Z.modulo => "fn ##name##(a: i64, b: i64) -> i64 { a.checked_rem(b).unwrap_or(a) }".*)
Extract Constant Corelib.BinNums.IntDef.Z.compare =>
"fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }".
Extract Constant Corelib.BinNums.IntDef.Z.of_N =>
"fn ##name##(&'a self, a: u64) -> i64 {
  use std::convert::TryFrom;
  i64::try_from(a).unwrap()
}".
Extract Constant Stdlib.ZArith.BinIntDef.Z.abs_N => "fn ##name#(&'a self, a: i64) -> u64 { a.unsigned_abs() }".
