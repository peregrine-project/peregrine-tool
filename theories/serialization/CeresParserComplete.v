(** * Completeness of the Ceres s-expression parser w.r.t. the Ceres printer

    CeresBS proves soundness of its parser ([CeresParserRoundtrip.PARSE_SEXPS_SOUND])
    but leaves completeness ("parsing a printed s-expression gives it back") as a TODO.
    This file proves it, for s-expressions whose atoms are printable in a way the
    parser accepts:
    - [Raw s] atoms must be nonempty, consist of atom characters, and not be
      readable as a number (otherwise they are read back as [Num]);
    - [Str s] atoms must only contain bytes that the printer does not escape as
      [\ddd] (the parser does not accept [\ddd] escapes): TAB, LF, CR,
      printable ASCII (32-126) and the bytes 128-244 (UTF-8);
    - [Num] atoms are always fine. *)

From Stdlib Require Import List ZArith Bool DecimalString DecimalPos DecimalZ Strings.Byte.
From MetaRocq.Utils Require Import bytestring.
From CeresBS Require Import CeresS CeresString CeresFormat CeresParserUtils
  CeresParserInternal CeresParser CeresRoundtrip.

Import ListNotations.
Local Open Scope bs_scope.

(** ** Which s-expressions can be printed and parsed back *)

Definition str_char_ok (c : byte) : bool :=
  ("009" =? c)%char2 || ("010" =? c)%char2 || ("013" =? c)%char2 ||
  is_printable c || is_utf_8 c.

Definition raw_ok (s : string) : bool :=
  match s with "" => false | _ => true end &&
  string_forall is_atom_char s &&
  match NilZero.int_of_string (String.to_string s) with None => true | Some _ => false end.

Definition atom_raw_okb (a : atom) : bool :=
  match a with Raw s => raw_ok s | _ => true end.

Definition atom_str_okb (a : atom) : bool :=
  match a with Str s => string_forall str_char_ok s | _ => true end.

Definition atom_okb (a : atom) : bool := atom_raw_okb a && atom_str_okb a.

Fixpoint sexp_forall_atoms (f : atom -> bool) (e : sexp) : bool :=
  match e with
  | Atom_ a => f a
  | List es => forallb (sexp_forall_atoms f) es
  end.

Definition sexp_okb : sexp -> bool := sexp_forall_atoms atom_okb.

Lemma sexp_forall_atoms_andb f g e :
  sexp_forall_atoms (fun a => f a && g a) e =
  sexp_forall_atoms f e && sexp_forall_atoms g e.
Proof.
  induction e using sexp__ind; cbn; [reflexivity|].
  induction H; cbn; [reflexivity|].
  rewrite H, IHForall.
  destruct (sexp_forall_atoms f x), (sexp_forall_atoms g x),
    (forallb (sexp_forall_atoms f) l), (forallb (sexp_forall_atoms g) l); reflexivity.
Qed.

Lemma sexp_okb_split e :
  sexp_okb e = sexp_forall_atoms atom_raw_okb e && sexp_forall_atoms atom_str_okb e.
Proof. apply sexp_forall_atoms_andb. Qed.

(** ** The printer, in direct style *)

Lemma bs_append_assoc (a b c : string) : (a ++ b) ++ c = a ++ (b ++ c).
Proof. induction a; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.

Lemma dstring_of_sexp_app (x : sexp) (s0 : string) :
  CeresFormat.dstring_of_sexp string_of_atom x s0 = string_of_sexp x ++ s0.
Proof.
  unfold string_of_sexp, string_of_sexp_.
  revert s0.
  induction x using sexp__ind; intros s0.
  - cbn. unfold DString.of_string. rewrite string_app_nil_r. reflexivity.
  - destruct xs as [|x xs]; [reflexivity|].
    inversion_clear H as [|? ? Hx Hxs].
    cbn [CeresFormat.dstring_of_sexp].
    unfold DString.app_string, DString.of_byte, id.
    rewrite Hx, (Hx (fold_right _ _ xs)).
    cbn [String.append]. f_equal.
    rewrite bs_append_assoc. f_equal.
    induction Hxs as [|y ys Hy Hys IH]; [reflexivity|].
    cbn [fold_right]. rewrite IH. cbn [String.append].
    rewrite Hy, (Hy (fold_right _ _ ys)). f_equal.
    rewrite bs_append_assoc. reflexivity.
Qed.

(** Direct-style equations for [string_of_sexp]. *)
Definition print_tail (xs : list sexp) : string :=
  fold_right (fun y acc => " " :: string_of_sexp y ++ acc) ")" xs.

Lemma string_of_sexp_atom a : string_of_sexp (Atom a) = string_of_atom a.
Proof. cbn. unfold DString.of_string. apply string_app_nil_r. Qed.

Lemma string_of_sexp_nil : string_of_sexp (List []) = "()".
Proof. reflexivity. Qed.

Lemma string_of_sexp_cons x xs :
  string_of_sexp (List (x :: xs)) = "(" :: string_of_sexp x ++ print_tail xs.
Proof.
  change (string_of_sexp (List (x :: xs))) with
    ("(" :: CeresFormat.dstring_of_sexp string_of_atom x
       (fold_right (fun y s => " " :: CeresFormat.dstring_of_sexp string_of_atom y s) (")" :: "") xs)).
  rewrite dstring_of_sexp_app. f_equal. f_equal.
  unfold print_tail. induction xs as [|y ys IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH, dstring_of_sexp_app. reflexivity.
Qed.

(** ** Running the parser on a string without errors *)

Fixpoint run (i : parser_state) (p : loc) (s : string) : option (parser_state * loc) :=
  match s with
  | "" => Some (i, p)
  | c :: s =>
    match next i p c with
    | inl _ => None
    | inr i' => run i' (N.succ p) s
    end
  end.

Lemma run_app i p s1 s2 :
  run i p (s1 ++ s2) =
  match run i p s1 with Some (i', p') => run i' p' s2 | None => None end.
Proof.
  revert i p; induction s1; intros; cbn; [reflexivity|].
  destruct next; auto.
Qed.

Lemma run_parse_sexps_ i p s1 s2 i' p' :
  run i p s1 = Some (i', p') -> parse_sexps_ i p (s1 ++ s2) = parse_sexps_ i' p' s2.
Proof.
  revert i p; induction s1; intros i p H; cbn in *; [congruence|].
  destruct next; [discriminate|]. eauto.
Qed.

Notation mk d u t :=
  {| parser_done := d; parser_stack := u; parser_cur_token := t |}.

(** After printing [e] starting in a state with no pending token, done list
    [d] and stack [u], the parser either has already pushed [e]
    (lists and strings) or holds the token of the atom [e]
    (raw atoms and numbers), which will be pushed by the next separator. *)
Definition pending (d : list sexp) (u : list symbol) (e : sexp) (st : parser_state) : Prop :=
  st = new_sexp d u e NoToken \/
  exists q tok, st = mk d u (SimpleToken q tok) /\ e = Atom (raw_or_num tok).

Lemma pending_next d u e st p c :
  pending d u e st -> is_atom_char c = false ->
  next st p c = next' (new_sexp d u e tt) p c.
Proof.
  intros [-> | (q & tok & -> & ->)] Hc.
  - destruct u; cbn; rewrite Hc; reflexivity.
  - cbn; rewrite Hc; reflexivity.
Qed.

Lemma new_sexp_cons {T : Set} d u e (t : T) :
  u <> [] -> new_sexp d u e t = mk d (Exp e :: u) t.
Proof. destruct u; [congruence|reflexivity]. Qed.

Lemma fold_stack_spec d p q u l r :
  _fold_stack d p r (map Exp (rev l) ++ Open q :: u) = inr (new_sexp d u (List (l ++ r)) NoToken).
Proof.
  revert r; induction l as [|x l IH] using rev_ind; intros r; [reflexivity|].
  rewrite rev_app_distr; cbn. rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma string_reverse_gen s r t :
  _string_reverse t (_string_reverse r s) = _string_reverse (s ++ t) r.
Proof. revert r; induction s; intros r; cbn; [reflexivity|]. rewrite IHs. reflexivity. Qed.

Lemma string_reverse_involutive s : _string_reverse "" (_string_reverse "" s) = s.
Proof. rewrite string_reverse_gen, string_app_nil_r. reflexivity. Qed.

(** *** Atoms *)

Lemma run_simple d u q0 tok q s :
  string_forall is_atom_char s = true ->
  exists q1 p', run (mk d u (SimpleToken q0 tok)) q s =
                Some (mk d u (SimpleToken q1 (_string_reverse tok s)), p').
Proof.
  revert q0 tok q; induction s as [|c s IH]; intros q0 tok q H; cbn in *.
  - eauto.
  - destruct (is_atom_char c); [|discriminate]. apply IH; assumption.
Qed.

Lemma run_token d u q s :
  s <> "" -> string_forall is_atom_char s = true ->
  exists q1 p', run (mk d u NoToken) q s =
                Some (mk d u (SimpleToken q1 (string_reverse s)), p').
Proof.
  destruct s as [|c s]; intros Hne H; [congruence|]. cbn in H |- *.
  destruct (is_atom_char c); [|discriminate]. apply run_simple; assumption.
Qed.

Lemma run_raw d u q s :
  raw_ok s = true ->
  exists st p', run (mk d u NoToken) q s = Some (st, p') /\ pending d u (Atom (Raw s)) st.
Proof.
  unfold raw_ok. intros H.
  destruct s as [|c s']; [discriminate|].
  apply andb_prop in H as [H Hnum]. apply andb_prop in H as [_ H].
  destruct (run_token d u q (c :: s') ltac:(discriminate) H) as (q1 & p' & Hrun).
  eexists _, _. split; [exact Hrun|]. right. eexists _, _. split; [reflexivity|].
  unfold raw_or_num, string_reverse. rewrite string_reverse_involutive.
  destruct NilZero.int_of_string; [discriminate|reflexivity].
Qed.

Lemma uint_atom_chars d :
  string_forall is_atom_char (String.of_string (NilEmpty.string_of_uint d)) = true.
Proof. induction d; cbn; try exact IHd; reflexivity. Qed.

Lemma string_of_Z_atom_chars n : string_forall is_atom_char (string_of_Z n) = true.
Proof.
  unfold string_of_Z. destruct (Z.to_int n) as [d|d]; [apply uint_atom_chars|].
  cbn [NilEmpty.string_of_int String.of_string string_forall].
  apply uint_atom_chars.
Qed.

Lemma NilEmpty_NilZero_uint d :
  d <> Decimal.Nil -> NilEmpty.string_of_uint d = NilZero.string_of_uint d.
Proof. destruct d; [congruence|..]; reflexivity. Qed.

Lemma string_of_Z_spec n :
  string_of_Z n <> "" /\
  raw_or_num (string_reverse (string_of_Z n)) = Num n.
Proof.
  destruct n as [|p|p]; [split; [discriminate|reflexivity]| |];
    pose proof (Unsigned.to_uint_nonnil p) as Hp;
    unfold string_of_Z; split.
  - change (Z.to_int (Z.pos p)) with (Decimal.Pos (Pos.to_uint p)).
    cbn [NilEmpty.string_of_int].
    destruct (Pos.to_uint p); [congruence|..]; discriminate.
  - unfold raw_or_num, string_reverse. rewrite string_reverse_involutive, bytestring_to_of.
    change (Z.to_int (Z.pos p)) with (Decimal.Pos (Pos.to_uint p)).
    cbn [NilEmpty.string_of_int]. rewrite NilEmpty_NilZero_uint by exact Hp.
    change (NilZero.string_of_uint (Pos.to_uint p)) with
      (NilZero.string_of_int (Decimal.Pos (Pos.to_uint p))).
    rewrite NilZero.isi by congruence.
    change (Decimal.Pos (Pos.to_uint p)) with (Z.to_int (Z.pos p)).
    rewrite DecimalZ.of_to. reflexivity.
  - change (Z.to_int (Z.neg p)) with (Decimal.Neg (Pos.to_uint p)).
    discriminate.
  - unfold raw_or_num, string_reverse. rewrite string_reverse_involutive, bytestring_to_of.
    change (Z.to_int (Z.neg p)) with (Decimal.Neg (Pos.to_uint p)).
    cbn [NilEmpty.string_of_int]. rewrite NilEmpty_NilZero_uint by exact Hp.
    change (Stdlib.Strings.String.String (Ascii.Ascii true false true true false true false false) (NilZero.string_of_uint (Pos.to_uint p))) with
      (NilZero.string_of_int (Decimal.Neg (Pos.to_uint p))).
    rewrite NilZero.isi by congruence.
    change (Decimal.Neg (Pos.to_uint p)) with (Z.to_int (Z.neg p)).
    rewrite DecimalZ.of_to. reflexivity.
Qed.

Lemma run_num d u q n :
  exists st p', run (mk d u NoToken) q (string_of_Z n) = Some (st, p') /\ pending d u (Atom (Num n)) st.
Proof.
  destruct (string_of_Z_spec n) as [Hne Hn].
  destruct (run_token d u q _ Hne (string_of_Z_atom_chars n)) as (q1 & p' & Hrun).
  eexists _, _. split; [exact Hrun|]. right. eexists _, _. split; [reflexivity|].
  rewrite Hn. reflexivity.
Qed.

Lemma run_str_body d u q0 tok q s rest :
  string_forall str_char_ok s = true ->
  exists p', run (mk d u (StrToken q0 tok EscNone)) q (_escape_string rest s) =
             run (mk d u (StrToken q0 (_string_reverse tok s) EscNone)) p' rest.
Proof.
  revert tok q; induction s as [|c s IH]; intros tok q H;
    cbn [string_forall _escape_string] in *; [eauto|].
  destruct (str_char_ok c) eqn:Hc; [|discriminate]. cbn [_string_reverse].
  unfold str_char_ok in Hc.
  destruct ("009" =? c)%char2 eqn:E9;
    [apply eqb_eq_byte in E9; subst c; cbn; apply IH; assumption|].
  destruct ("010" =? c)%char2 eqn:E10;
    [apply eqb_eq_byte in E10; subst c; cbn; apply IH; assumption|].
  destruct ("013" =? c)%char2 eqn:E13;
    [apply eqb_eq_byte in E13; subst c; cbn; apply IH; assumption|].
  destruct ("""" =? c)%char2 eqn:Edq;
    [apply eqb_eq_byte in Edq; subst c; cbn; apply IH; assumption|].
  destruct ("\" =? c)%char2 eqn:Ebs;
    [apply eqb_eq_byte in Ebs; subst c; cbn; apply IH; assumption|].
  cbn [orb] in Hc. rewrite Hc.
  cbn. rewrite Ebs, Edq, Hc. apply IH; assumption.
Qed.

Lemma run_str d u q s :
  string_forall str_char_ok s = true ->
  exists st p', run (mk d u NoToken) q (escape_string s) = Some (st, p') /\ pending d u (Atom (Str s)) st.
Proof.
  intros H. unfold escape_string. cbn [run].
  change (next (mk d u NoToken) q """") with
    (@inr error parser_state (mk d u (StrToken q "" EscNone))).
  destruct (run_str_body d u q "" (N.succ q) s """" H) as [p' ->].
  eexists _, _. split; [reflexivity|]. left.
  cbn. rewrite string_reverse_involutive. reflexivity.
Qed.

Lemma run_atom d u q a :
  atom_okb a = true ->
  exists st p', run (mk d u NoToken) q (string_of_sexp (Atom a)) = Some (st, p') /\ pending d u (Atom a) st.
Proof.
  rewrite string_of_sexp_atom. unfold atom_okb.
  destruct a as [n|s|s]; cbn; intros H.
  - apply run_num.
  - apply run_str. exact H.
  - apply run_raw. now destruct (raw_ok s).
Qed.

(** *** S-expressions *)

Definition run_spec (e : sexp) : Prop :=
  forall d u q, exists st p',
    run (mk d u NoToken) q (string_of_sexp e) = Some (st, p') /\ pending d u e st.

Lemma run_tail d q0 u xs :
  Forall (fun e => sexp_okb e = true -> run_spec e) xs ->
  forallb sexp_okb xs = true ->
  forall l x st q, pending d (map Exp (rev l) ++ Open q0 :: u) x st ->
  exists p', run st q (print_tail xs) = Some (new_sexp d u (List (l ++ x :: xs)) NoToken, p').
Proof.
  induction 1 as [|y ys Hy Hys IH]; intros Hok l x st q Hp; cbn [print_tail fold_right] in *.
  - cbn [run]. rewrite (pending_next _ _ _ _ _ _ Hp) by reflexivity.
    change (next' ?i q ")") with (_fold_stack (parser_done i) q [] (parser_stack i)).
    rewrite new_sexp_cons by (intros Hnil; apply app_eq_nil in Hnil as [_ Hnil]; discriminate).
    cbn [parser_done parser_stack].
    change (Exp x :: map Exp (rev l) ++ Open q0 :: u)%list with
      (map Exp (x :: rev l) ++ Open q0 :: u)%list.
    replace (x :: rev l)%list with (rev (l ++ [x])) by (rewrite rev_app_distr; reflexivity).
    rewrite fold_stack_spec, app_nil_r. cbn. eauto.
  - apply andb_prop in Hok as [Hoky Hokys].
    cbn [run]. rewrite (pending_next _ _ _ _ _ _ Hp) by reflexivity.
    change (next' ?i q " ") with (@inr error parser_state (mk (parser_done i) (parser_stack i) NoToken)).
    rewrite new_sexp_cons by (intros Hnil; apply app_eq_nil in Hnil as [_ Hnil]; discriminate).
    cbn [parser_done parser_stack].
    destruct (Hy Hoky d (Exp x :: map Exp (rev l) ++ Open q0 :: u)%list (N.succ q))
      as (st1 & p1 & Hrun1 & Hp1).
    rewrite run_app, Hrun1.
    change (Exp x :: map Exp (rev l) ++ Open q0 :: u)%list with
      (map Exp (x :: rev l) ++ Open q0 :: u)%list in Hp1.
    replace (x :: rev l)%list with (rev (l ++ [x])) in Hp1 by (rewrite rev_app_distr; reflexivity).
    destruct (IH Hokys _ _ _ p1 Hp1) as [p' Hrun]. unfold print_tail in Hrun. rewrite Hrun.
    rewrite <- app_assoc. cbn. eauto.
Qed.

Lemma run_sexp e : sexp_okb e = true -> run_spec e.
Proof.
  induction e as [a|xs IH] using sexp__ind; intros Hok d u q.
  - apply run_atom. exact Hok.
  - destruct xs as [|x xs].
    + eexists _, _. split; [reflexivity|]. left. reflexivity.
    + inversion_clear IH as [|? ? Hx Hxs].
      cbn [sexp_okb sexp_forall_atoms forallb] in Hok. fold sexp_okb in Hok.
      apply andb_prop in Hok as [Hokx Hokxs].
      rewrite string_of_sexp_cons. cbn [run].
      change (next (mk d u NoToken) q "(") with
        (@inr error parser_state (mk d (Open q :: u)%list NoToken)).
      destruct (Hx Hokx d (Open q :: u)%list (N.succ q)) as (st1 & p1 & Hrun1 & Hp1).
      rewrite run_app, Hrun1.
      destruct (run_tail d q u xs Hxs Hokxs [] x st1 p1 Hp1) as [p' Hrun].
      rewrite Hrun. eexists _, _. split; [reflexivity|]. left. reflexivity.
Qed.

(** ** Completeness of the parser *)

Lemma run_whitespace d e st q ws :
  pending d [] e st -> string_forall is_whitespace ws = true ->
  exists st' p', run st q ws = Some (st', p') /\ pending d [] e st'.
Proof.
  revert st q. induction ws as [|c ws IH]; intros st q Hp Hws.
  { exists st, q. split; [reflexivity|exact Hp]. }
  cbn [string_forall] in Hws.
  destruct (is_whitespace c) eqn:Hc; [|discriminate].
  assert (is_atom_char c = false)
    by (destruct c; try discriminate; reflexivity).
  cbn [run]. rewrite (pending_next _ _ _ _ _ _ Hp) by assumption.
  replace (next' (new_sexp d [] e tt) q c) with
    (@inr error parser_state (new_sexp d [] e NoToken))
    by (destruct c; try discriminate; reflexivity).
  apply IH; [left; reflexivity | exact Hws].
Qed.

(** Parsing a printed s-expression, possibly followed by whitespace, gives it back. *)
Theorem parse_sexp_string_of_sexp e ws :
  sexp_okb e = true -> string_forall is_whitespace ws = true ->
  parse_sexp (string_of_sexp e ++ ws) = inr e.
Proof.
  intros Hok Hws.
  destruct (run_sexp e Hok [] [] 0%N) as (st & p & Hrun & Hp).
  destruct (run_whitespace [] e st p ws Hp Hws) as (st' & p' & Hrun' & Hp').
  unfold parse_sexp.
  pose proof (run_parse_sexps_ _ _ _ "" _ _ Hrun') as Hws'.
  rewrite string_app_nil_r in Hws'. cbn in Hws'.
  rewrite (run_parse_sexps_ _ _ _ _ _ _ Hrun), Hws'.
  destruct Hp' as [-> | (q & tok & -> & ->)]; reflexivity.
Qed.

Corollary parse_sexp_string_of_sexp' e :
  sexp_okb e = true -> parse_sexp (string_of_sexp e) = inr e.
Proof.
  intros Hok. rewrite <- (string_app_nil_r (string_of_sexp e)).
  apply parse_sexp_string_of_sexp; [exact Hok | reflexivity].
Qed.

Theorem parse_sexps_string_of_sexp e ws :
  sexp_okb e = true -> string_forall is_whitespace ws = true ->
  parse_sexps (string_of_sexp e ++ ws) = inr [e].
Proof.
  intros Hok Hws.
  destruct (run_sexp e Hok [] [] 0%N) as (st & p & Hrun & Hp).
  destruct (run_whitespace [] e st p ws Hp Hws) as (st' & p' & Hrun' & Hp').
  unfold parse_sexps.
  pose proof (run_parse_sexps_ _ _ _ "" _ _ Hrun') as Hws'.
  rewrite string_app_nil_r in Hws'. cbn in Hws'.
  rewrite (run_parse_sexps_ _ _ _ _ _ _ Hrun), Hws'.
  destruct Hp' as [-> | (q & tok & -> & ->)]; reflexivity.
Qed.
