From Stdlib Require Import List NArith ZArith (* String *).
From MetaRocq.Utils Require Import bytestring.
From Ceres Require Import Ceres CeresParser CeresParserInternal.

Import ListNotations.
Local Open Scope bs_scope.

Definition s : unit + (nat * bool * unit) := inr (1, false, tt).
Definition test_to_string_s : to_string s = "(inr ((1 false) tt))"
  := eq_refl.

Definition roundtrip {A} `{Serialize A} `{Deserialize A} : A -> Prop :=
  fun a => from_sexp (to_sexp a) = inr a.

Lemma roundtrip_bool : Forall roundtrip [true; false].
Proof. repeat constructor. Qed.

Lemma roundtrip_nat : Forall roundtrip [0; 1; 2].
Proof. repeat constructor. Qed.

Lemma roundtrip_Z : Forall roundtrip [-2; -1; 0; 1; 2]%Z.
Proof. repeat constructor. Qed.

Lemma roundtrip_N : Forall roundtrip [0; 1; 2]%N.
Proof. repeat constructor. Qed.

Lemma roundtrip_pair : roundtrip (0, true).
Proof. reflexivity. Qed.

Lemma roundtrip_sum : Forall roundtrip [inl tt; inr 0].
Proof. repeat constructor. Qed.

Lemma roundtrip_list : Forall roundtrip [[]; [0]; [0;1]; [0;1;2]].
Proof. repeat constructor. Qed.

Lemma roundtrip_s : roundtrip s.
Proof. reflexivity. Qed.

From Stdlib Require Import Strings.Byte.

Lemma parse_1 : parse_sexps "a" = inr [Atom "a"].
Proof. reflexivity. Qed.

Lemma parse_2 : parse_sexps """a""" = inr [Atom (Str "a")].
Proof. reflexivity. Qed.

Lemma parse_3 : parse_sexps "3" = inr [Atom 3%Z].
Proof. reflexivity. Qed.

Lemma parse_4 : parse_sexps "-3" = inr [Atom (-3)%Z].
Proof. reflexivity. Qed.

Lemma parse_5 : parse_sexps "(ab)" = inr [List [Atom "ab"]].
Proof. reflexivity. Qed.

Lemma parse_6 : parse_sexps "(ab cd)" = inr [List [Atom "ab"; Atom "cd"]].
Proof. reflexivity. Qed.

Lemma parse_7 : parse_sexps "(a b c)" = inr [List [Atom "a"; Atom "b"; Atom "c"]].
Proof. reflexivity. Qed.

Lemma parse_8 : parse_sexps "ab cd" = inr [Atom "ab"; Atom "cd"].
Proof. reflexivity. Qed.

Lemma parse_9 : parse_sexps "ab (cd (ef gh) ij) kl"
              = inr [Atom "ab"; List [Atom "cd"; List [Atom "ef"; Atom "gh"]; Atom "ij"]; Atom "kl"].
Proof. reflexivity. Qed.

Local Open Scope N_scope.
Local Open Scope sexp_scope.

Lemma parse_10 :
  let '(r1, p1, s0) := parse_sexps_ initial_state 0 "(1)(2)3" in
  let (e1, s1) := get_one s0 in
  let (e2, s2) := get_one s1 in
  let (e3, s3) := get_one s2 in
  let '(r2, p2, s4) := parse_sexps_ s2 p1 "4 )" in
  let (e4, s5) := get_one s4 in
  e1 = Some [Atom 1%Z] /\
  e2 = Some [Atom 2%Z] /\
  e3 = None /\
  e4 = Some (Atom 34%Z).
Proof. split; split; split; reflexivity. Qed.

Lemma parse_11
  : parse_sexps "a.b a-b a? a! || hi' +1 a/b"
  = inr [Atom "a.b"; Atom "a-b"; Atom "a?"; Atom "a!"; Atom "||"; Atom "hi'"; Atom "+1"; Atom "a/b"]%list.
Proof. reflexivity. Qed.

(**)

(* Test that recursive deserializers are supported. *)
Definition Deserialize_unary : Deserialize nat :=
  fix deser_nat l (e : sexp) {struct e} :=
    Deser.match_con (A := nat) "nat"
      [ ("Z", 0%nat) ]
      [ ("S", Deser.con1 S deser_nat) ] l e.
