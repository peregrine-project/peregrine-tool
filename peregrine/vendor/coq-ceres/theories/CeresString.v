(** * String utilities *)

(* begin hide *)
From Stdlib Require Import
  Setoid
  Bool DecidableClass List Arith ZArith NArith Strings.Byte (* Ascii String *) Decimal DecimalString.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require ByteCompare ByteCompareSpec.

Local Open Scope bs_scope.

(* end hide *)

(* Booleans *)

Inductive reflect_eq {A} (x : A) : A -> bool -> Prop :=
| reflect_eq_true : reflect_eq x x true
| reflect_eq_false y : x <> y -> reflect_eq x y false
.

(* [Bool.eqb_spec], which doesn't exist on Coq 8.8 *)
Lemma eqb_eq_bool x y : reflect (x = y) (Bool.eqb x y).
Proof.
  destruct (Bool.eqb _ _) eqn:H;
    constructor; [ apply eqb_prop | apply eqb_false_iff ]; auto.
Defined.

Lemma eqb_eq_bool' x y : reflect_eq x y (Bool.eqb x y).
Proof.
  destruct x, y; constructor; discriminate.
Qed.

Definition compcomp (x y : comparison) : comparison :=
  match x with
  | Eq => y
  | Lt => Lt
  | Gt => Gt
  end.

Declare Scope compare_scope.
Delimit Scope compare_scope with compare.
Infix "::" := compcomp : compare_scope.

Definition compb (x y : bool) : comparison :=
  match x, y with
  | false, false => Eq
  | false, true => Lt
  | true, false => Gt
  | true, true => Eq
  end.

(* Strings and characters *)

Infix "::" := String.string : string_scope.

Local Open Scope lazy_bool_scope.

(* Backport #8063 to Coq 8.8 *)
Definition eqb_byte (a b : byte) : bool :=
  ByteCompare.eqb a b.
Arguments eqb_byte : simpl never.

(* Note: the most significant bit is on the right. *)
Definition byte_compare (a b : byte) : comparison :=
  ByteCompare.compare a b.

Definition leb_byte (a b : byte) : bool :=
  match byte_compare a b with
  | Gt => false
  | _ => true
  end.

Declare Scope char2_scope.
Delimit Scope char2_scope with char2.
Infix "=?" := eqb_byte : char2_scope.
Infix "<=?" := leb_byte : char2_scope.

Definition eqb_eq {A} (eqb : A -> A -> bool) :=
  forall a b, eqb a b = true <-> a = b.

Lemma eqb_eq_byte : eqb_eq eqb_byte.
Proof with auto.
  split; intros H.
  - rewrite ByteCompareSpec.eqb_compare in H.
    destruct (ByteCompareSpec.compare_spec a b); auto; discriminate.
  - apply N.eqb_eq.
    f_equal.
    assumption.
Defined.

Lemma eqb_eq_byte' c0 c1 :
  reflect_eq c0 c1 (c0 =? c1)%char2.
Proof.
  unfold eqb_byte.
  rewrite ByteCompareSpec.eqb_compare.
  destruct (ByteCompareSpec.compare_spec c0 c1).
  - subst. constructor.
  - apply ByteCompareSpec.lt_not_eq in H.
    constructor. auto.
  - apply ByteCompareSpec.lt_not_eq in H.
    constructor. auto.
Qed.

Lemma neqb_neq_byte a b : eqb_byte a b = false <-> a <> b.
Proof.
  etransitivity.
  - symmetry; apply not_true_iff_false.
  - apply not_iff_compat, eqb_eq_byte.
Qed.

Global
Instance Decidable_eq_byte : forall (a b : byte), Decidable (a = b).
Proof.
  exact (fun a b : byte =>
           {| Decidable_witness := eqb_byte a b;
              Decidable_spec := eqb_eq_byte a b |}).
Defined.

Ltac match_byte :=
  repeat
    match goal with
    | [ |- context E [ eqb_byte ?x ?y ] ] =>
      destruct (eqb_eq_byte' x y)
    end.

Fixpoint eqb_string s1 s2 : bool :=
  match s1, s2 with
  | String.EmptyString, String.EmptyString => true
  | String.String c1 s1', String.String c2 s2' => eqb_byte c1 c2 &&& eqb_string s1' s2'
  | _,_ => false
  end.

Lemma eqb_eq_string : eqb_eq eqb_string.
Proof with auto.
  intro s1.
  induction s1; intros []; split; intro H; try discriminate...
  - simpl in H.
    apply andb_prop in H.
    destruct H.
    apply eqb_eq_byte in H.
    apply IHs1 in H0.
    f_equal...
  - inversion H; subst.
    simpl.
    apply andb_true_intro.
    split.
    + apply eqb_eq_byte...
    + apply IHs1...
Defined.

Global
Instance Decidable_eq_string : forall (s1 s2 : string), Decidable (s1 = s2).
Proof.
  exact (fun s1 s2 : string =>
           {| Decidable_witness := eqb_string s1 s2;
              Decidable_spec := eqb_eq_string s1 s2 |}).
Defined.

Notation "x :: y" := (String.String x y) : bs_scope.

Fixpoint string_elem (c : byte) (s : string) : bool :=
  match s with
  | "" => false
  | c' :: s => eqb_byte c c' ||| string_elem c s
  end%bs.

Fixpoint string_forall (f : byte -> bool) (s : string) : bool :=
  match s with
  | "" => true
  | c :: s => f c &&& string_forall f s
  end%bs.

Fixpoint _string_reverse (r s : string) : string :=
  match s with
  | "" => r
  | c :: s => _string_reverse (c :: r) s
  end%bs.

Definition string_reverse : string -> string := _string_reverse ""%bs.

Lemma string_app_nil_r (s : string) : (s ++ "")%bs = s.
Proof.
  induction s; [ auto | cbn; rewrite IHs; auto ].
Qed.

Lemma not_string_elem_app c s1 s2
  : string_elem c s1 = false ->
    string_elem c s2 = false ->
    string_elem c (s1 ++ s2) = false.
Proof.
  induction s1; cbn; auto.
  destruct (c =? b)%char2; try discriminate; auto.
Qed.

Lemma not_string_elem_head c c' s
  : string_elem c (c' :: s) = false -> c <> c'.
Proof.
  cbn; destruct (eqb_eq_byte' c c'); discriminate + auto.
Qed.

Lemma not_string_elem_singleton c c'
  : c <> c' -> string_elem c (c' :: "") = false.
Proof.
  rewrite <- neqb_neq_byte.
  intros H; cbn; rewrite H.
  reflexivity.
Qed.

(** Separate elements with commas. *)
Fixpoint comma_sep (xs : list string) : string :=
  match xs with
  | nil => ""
  | x :: nil => x
  | x :: xs => (x ++ ", " ++ comma_sep xs)%bs
  end%list.

Notation newline := ("010" :: "")%bs.

Section ByteTest.

Local Open Scope char2_scope.

(** Is a character printable? The character is given by its ASCII code. *)
Definition is_printable (c : byte) : bool :=
  (  (" " <=? c)%char2 (* 32 = SPACE *)
  && (c <=? "~")%char2 (* 126 = ~ *)
  ).

(** Is a character part of a non-ascii utf-8 code point?
  Doesn't check if it is a valid utf-8 byte sequence
*)
Definition is_utf_8 (c : byte) : bool :=
  (  ("128" <=? c)%char2 (* 0x80 *)
  && (c <=? "244")%char2 (* 0xF4 *)
  ).

Definition is_whitespace (c : byte) : bool :=
  match c with
  | " " | "010" | "013" => true
  | _ => false
  end%byte.

Definition is_digit (c : byte) : bool :=
  ("0" <=? c) &&& (c <=? "9").

Definition is_upper (c : byte) : bool :=
  ("A" <=? c) &&& (c <=? "Z").

Definition is_lower (c : byte) : bool :=
  ("a" <=? c) &&& (c <=? "z").

Definition is_alphanum (c : byte) : bool :=
  is_upper c |||
  is_lower c |||
  is_digit c.

End ByteTest.

(** ** Escape string *)

(** The [ascii] units digit of a [nat]. *)
Local Definition _units_digit (n : nat) : byte :=
  Ascii.byte_of_ascii (Ascii.ascii_of_nat ((n mod 10) + 48 (* 0 *))).

(** The hundreds, tens, and units digits of a [nat]. *)
Local Definition _three_digit (n : nat) : string :=
  let n0 := _units_digit n in
  let n1 := _units_digit (n / 10) in
  let n2 := _units_digit (n / 100) in
  (n2 :: n1 :: n0 :: String.EmptyString).

(** Helper for [escape_string] *)
Fixpoint _escape_string (_end s : string) : string :=
  match s with
  | String.EmptyString => _end
  | (c :: s')%bs =>
    let escaped_s' := _escape_string _end s' in
    if ("009" =? c)%char2 (* 9 = TAB *) then
      "\" :: "t" :: escaped_s'
    else if ("010" =? c)%char2 (* 10 = NEWLINE *) then
      "\" :: "n" :: escaped_s'
    else if ("013" =? c)%char2 (* 13 = CARRIAGE RETURN *) then
      "\" :: "r" :: escaped_s'
    else if ("""" =? c)%char2 (* DOUBLEQUOTE *) then
      "\" :: """" :: escaped_s'
    else if ("\" =? c)%char2 (* BACKSLASH *) then
      "\" :: "\" :: escaped_s'
    else
      if is_printable c || is_utf_8 c then
        c :: escaped_s'
      else
        let n := Ascii.nat_of_ascii (Ascii.ascii_of_byte c) in
        "\" :: _three_digit n ++ escaped_s'
  end.

(** Escape a string so it can be shown in a terminal. *)
Definition escape_string (s : string) : string :=
  String.String """" (_escape_string """" s).

(** ** Unescape string *)

(** Read an [ascii] digit into a [nat]. *)
Definition digit_of_byte (c : byte) : option nat :=
  let n := Ascii.nat_of_ascii (Ascii.ascii_of_byte c) in
  if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
    Some (n - 48)
  else
    None.

(** The inverse of [three digit]. *)
Local Definition _unthree_digit (c2 c1 c0 : byte) : option byte :=
  let doa := digit_of_byte in
  match doa c2, doa c1, doa c0 with
  | Some n2, Some n1, Some n0 =>
    Some (Ascii.byte_of_ascii (Ascii.ascii_of_nat (n2 * 100 + n1 * 10 + n0)))
  | _, _, _ => None
  end.

(** Helper for [unescape_string]. *)
Local Fixpoint _unescape_string (s : string) : option string :=
  match s with
  | String.String c s' =>
    if eqb_byte c """" then
      match s' with
      | String.EmptyString => Some String.EmptyString
      | _ => None
      end
    else if eqb_byte c "\" then
      match s' with
      | String.String c2 s'' =>
        if eqb_byte c2 "n" then
          option_map (String.String "010") (_unescape_string s'')
        else if eqb_byte c2 "r" then
          option_map (String.String "013") (_unescape_string s'')
        else if eqb_byte c2 "t" then
          option_map (String.String "009") (_unescape_string s'')
        else if eqb_byte c2 "\" then
          option_map (String.String "\") (_unescape_string s'')
        else if eqb_byte c2 """" then
          option_map (String.String """") (_unescape_string s'')
        else
          match s'' with
          | String.String c1 (String.String c0 s''') =>
            match _unthree_digit c2 c1 c0 with
            | Some c' => option_map (String.String c')
                                    (_unescape_string s''')
            | None => None
            end
          | _ => None
          end
      | _ => None
      end
    else
      option_map (String.String c) (_unescape_string s')
  | _ => None
  end.

(** The inverse of [escape_string]. *)
Definition unescape_string (s : string) : option string :=
  match s with
  | ("""" :: s')%bs => _unescape_string s'
  | (_ :: _)%bs => None
  | String.EmptyString => None
  end.

(** ** Convert numbers to string *)

Import NilEmpty.

Definition string_of_nat (n : nat) : string :=
  String.of_string (string_of_uint (Nat.to_uint n)).

Definition string_of_Z (n : Z) : string :=
  String.of_string (string_of_int (Z.to_int n)).

Definition string_of_N (n : N) : string :=
  string_of_Z (Z.of_N n).

Definition string_of_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Module DString.

(** Difference lists for fast append. *)
Definition t : Type := string -> string.

Definition of_string (s : string) : t := fun s' => (s ++ s')%bs.
Definition of_byte (c : byte) : t := fun s => (c :: s)%bs.
Definition app_string : t -> string -> string := id.

End DString.

Coercion DString.of_string : string >-> DString.t.
Coercion DString.of_byte : byte >-> DString.t.

(* Declare Scope dstring_scope. *)
Declare Scope dstring_scope.
Delimit Scope dstring_scope with dstring.
Bind Scope dstring_scope with DString.t.
Notation "a ++ b" := (fun s => DString.app_string a (DString.app_string b s))
  : dstring_scope.
