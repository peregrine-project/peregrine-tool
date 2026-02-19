From Stdlib Require Import
(*   Ascii
  String *)
  Strings.Byte
  List
  ZArith
  DecimalString.
From MetaRocq.Utils Require Import bytestring.
From Ceres Require Import
  CeresUtils
  CeresS
  CeresString
  CeresParser
  CeresParserUtils
  CeresParserInternal
  CeresParserRoundtrip.

Import ListNotations.

(* * Lemmas *)

Lemma atom_token_atom s
  : atom_string (string_reverse s) ->
    atom_token (raw_or_num s) (Token.Atom (string_reverse s)).
Proof.
  unfold raw_or_num. remember (string_reverse _) as s' eqn:E; clear E s.
  destruct NilZero.int_of_string eqn:Eios; intros H.
  - constructor. assumption.
  - constructor.
Qed.

Lemma whitespace_no_atom c
  : is_whitespace c = true -> is_atom_char c = false.
Proof.
  repeat match goal with
  | [ c : _ |- _ ] => destruct c; clear c; try discriminate
  end; cbn; reflexivity.
Qed.
Local Hint Resolve whitespace_no_atom : ceres.

Lemma list_sexp_tokens_singleton e ts
  : sexp_tokens e ts ->
    list_sexp_tokens [e] ts.
Proof.
  rewrite <- (app_nil_r ts) at 2.
  constructor; auto with ceres.
Qed.
Local Hint Resolve list_sexp_tokens_singleton : ceres.

Lemma list_sexp_tokens_app es1 es2 ts1 ts2
  : list_sexp_tokens es1 ts1 ->
    list_sexp_tokens es2 ts2 ->
    list_sexp_tokens (es1 ++ es2) (ts1 ++ ts2).
Proof.
  induction 1; cbn.
  - auto.
  - rewrite <- app_assoc; constructor; auto.
Qed.

Lemma string_app_assoc (s0 s1 s2 : string)
  : ((s0 ++ s1) ++ s2 = s0 ++ (s1 ++ s2))%bs.
Proof.
  induction s0; cbn; [ auto | rewrite IHs0; auto ].
Qed.

Lemma after_atom_string_snoc c s s' more :
  is_atom_char c = false ->
  after_atom_string more s ->
  after_atom_string false (s ++ c :: s')%bs.
Proof.
  intros Hc []; constructor; auto.
Qed.
Local Hint Resolve after_atom_string_snoc : ceres.

Lemma token_string_open_snoc more ts s :
  token_string more ts s ->
  token_string false (ts ++ [Token.Open]) (s ++ "(")%bs.
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ "("%bs); auto with ceres.
  eauto using token_string_atom with ceres.
Qed.

Lemma token_string_close_snoc more ts s :
  token_string more ts s ->
  token_string false (ts ++ [Token.Close]) (s ++ ")")%bs.
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ ")"%bs); auto with ceres.
  eauto using token_string_atom with ceres.
Qed.

Lemma token_string_atom_snoc ts s s1 :
  atom_string s1 ->
  token_string false ts s ->
  token_string true (ts ++ [Token.Atom s1]) (s ++ s1)%bs.
Proof.
  induction 2; cbn; try rewrite (string_app_assoc _ _ s1); auto with ceres.
  - rewrite <- string_app_nil_r at 2. apply token_string_atom; auto with ceres.
  - constructor; auto.
    inversion H1; cbn. constructor; auto.
Qed.

Lemma token_string_newline_snoc more s ts
  : token_string more ts s ->
    token_string false ts (s ++ newline)%bs.
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ newline); auto with ceres.
  - change newline with (newline ++ "")%bs. apply token_string_spaces; constructor.
  - eauto with ceres.
Qed.

Lemma token_string_comment_snoc more s s_com ts
  : token_string more ts s ->
    token_string false ts (s ++ ";" ++ s_com ++ newline)%bs.
Proof.
  induction 1; cbn; try rewrite string_app_assoc; auto with ceres.
  - change newline with (newline ++ "")%bs.
    change (?x :: ?y ++ ?z)%bs with ((x :: y) ++ z)%bs; rewrite <- string_app_assoc.
    apply token_string_comment; constructor.
  - eauto with ceres.
Qed.

Lemma token_string_string_snoc more s s_str ts
  : token_string more ts s ->
    token_string false (ts ++ [Token.Str s_str]) (s ++ """" ++ _escape_string "" s_str ++ """")%bs.
Proof.
  induction 1; cbn; try rewrite string_app_assoc; auto with ceres.
  - rewrite <- (string_app_nil_r (_ :: _)%bs).
    do 2 (constructor; eauto with ceres).
  - eauto with ceres.
Qed.

(* * Parser state *)

Inductive stack_tokens : list symbol -> list Token.t -> Prop :=
| stack_tokens_nil : stack_tokens [] []
| stack_tokens_open p us ts
  : stack_tokens us ts ->
    stack_tokens (Open p :: us) (ts ++ [Token.Open])
| stack_tokens_sexp e us ts ts0
  : sexp_tokens e ts0 ->
    stack_tokens us ts ->
    stack_tokens (Exp e :: us) (ts ++ ts0)
.
Local Hint Constructors stack_tokens : ceres.

Inductive stack_end_last : list symbol -> Prop :=
| stack_end_last_last p : stack_end_last [Open p]
| stack_end_last_cons u us : stack_end_last us -> stack_end_last (u :: us)
.

Inductive stack_end : list symbol -> Prop :=
| stack_end_nil : stack_end []
| stack_end_nonempty us : stack_end_last us -> stack_end us
.
Local Hint Constructors stack_end : ceres.

Lemma stack_end_cons v u us
  : stack_end (u :: us) ->
    stack_end (v :: u :: us).
Proof.
  inversion 1; do 2 constructor; auto.
Qed.
Local Hint Resolve stack_end_cons : ceres.

Lemma stack_end_cons_Open p us
  : stack_end us ->
    stack_end (Open p :: us).
Proof.
  inversion 1.
  - do 2 constructor.
  - inversion H0; do 3 (constructor; auto).
Qed.
Local Hint Resolve stack_end_cons_Open : ceres.

Lemma stack_end_inv u us
  : stack_end (u :: us) ->
    stack_end us.
Proof.
  inversion 1. inversion H0; auto with ceres.
Qed.
Local Hint Resolve stack_end_inv : ceres.

Definition escape_to_string (e : escape) : string :=
  match e with
  | EscBackslash => "\"
  | EscNone => ""
  end%bs.

Definition no_newline (s : string) : Prop :=
  string_elem "010" s = false.

Lemma is_atom_singleton (c : byte)
  : is_atom_char c = true -> atom_string (c :: "")%bs.
Proof. intros E; constructor; cbn; discriminate + rewrite E; reflexivity. Qed.
Local Hint Resolve is_atom_singleton : ceres.

Lemma is_atom_app (s : string) (c : byte)
  : atom_string s -> is_atom_char c = true -> atom_string (s ++ c :: "")%bs.
Proof.
  intros [_ Hs] Hc; constructor.
  - destruct s; discriminate.
  - revert Hs; unfold atom_string; induction s; cbn; intros.
    + rewrite Hc; auto.
    + destruct (is_atom_char b); discriminate + rewrite IHs; auto.
Qed.
Local Hint Resolve is_atom_app : ceres.

Inductive str_token_string (tok : string) : escape -> string -> Prop :=
| str_token_string_EscBackslash
  : str_token_string tok EscBackslash ("""" :: _escape_string "" (string_reverse tok) ++ "\")%bs
| str_token_string_EscNone
  : str_token_string tok EscNone ("""" :: _escape_string "" (string_reverse tok))%bs
.

Lemma str_token_string_new : str_token_string ""%bs EscNone """"%bs.
Proof. constructor. Qed.

Lemma more_ok_str_token more tok e s
  : str_token_string tok e s ->
    more_ok more s.
Proof.
  intros []; auto using more_ok_cons.
Qed.

Ltac match_match :=
  match goal with
  | [ |- context E [ match ?x with _ => _ end ] ] =>
    let Ex := fresh "H" in
    destruct x eqn:Ex
  end.

Lemma escape_string_newline s
  : (_escape_string "" s ++ "\n")%bs = _escape_string ""%bs (s ++ newline)%bs.
Proof.
  induction s; auto; cbn.
  match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma escape_string_backslash s
  : (_escape_string "" s ++ "\\")%bs = _escape_string ""%bs (s ++ "\")%bs.
Proof.
  induction s; auto; cbn.
  match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma escape_string_dquote s
  : (_escape_string "" s ++ "\""")%bs = _escape_string ""%bs (s ++ """")%bs.
Proof.
  induction s; auto; cbn.
  match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma escape_string_tab s
  : (_escape_string "" s ++ "\t")%bs = _escape_string ""%bs (s ++ ("009" :: ""))%bs.
Proof.
  induction s; auto; cbn.
  match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma escape_string_carriage_return s
  : (_escape_string "" s ++ "\r")%bs = _escape_string ""%bs (s ++ ("013" :: ""))%bs.
Proof.
  induction s; auto; cbn.
  match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma escape_string_regular c s
  : is_printable c = true \/ is_utf_8 c = true ->
    """"%byte <> c ->
    "\"%byte <> c ->
    (_escape_string "" s ++ c :: "")%bs = _escape_string ""%bs (s ++ c :: "")%bs.
Proof.
  intros H1 H2 H3.
  induction s; cbn.
  - match_byte; try match_match; cbn; destruct H1; try (discriminate + contradiction + auto).
    + apply Bool.orb_false_elim in H7 as [].
      rewrite H7 in H1. discriminate.
    + apply Bool.orb_false_elim in H7 as [].
      rewrite H8 in H1. discriminate.
  - match_byte; try match_match; cbn; rewrite IHs; reflexivity.
Qed.

Lemma _string_reverse_app s0 s1 s2
  : _string_reverse (s1 ++ s0)%bs s2 = (_string_reverse s1 s2 ++ s0)%bs.
Proof.
  revert s1; induction s2 as [ | c s2 IH ]; cbn; intros; auto.
  exact (IH (c :: s1)%bs).
Qed.

Lemma string_reverse_cons c s
  : string_reverse (c :: s)%bs = (string_reverse s ++ c :: "")%bs.
Proof.
  apply (_string_reverse_app (c :: "") "")%bs.
Qed.

Lemma str_token_string_newline tok s
  : str_token_string tok EscBackslash s ->
    str_token_string ("010" :: tok)%bs EscNone (s ++ "n")%bs.
Proof.
  inversion 1; cbn.
  rewrite string_app_assoc, escape_string_newline, <- string_reverse_cons.
  constructor.
Qed.

Lemma str_token_string_backslash tok s
  : str_token_string tok EscBackslash s ->
    str_token_string ("\" :: tok)%bs EscNone (s ++ "\")%bs.
Proof.
  inversion 1; cbn.
  rewrite string_app_assoc, escape_string_backslash, <- string_reverse_cons.
  constructor.
Qed.

Lemma str_token_string_dquote tok s
  : str_token_string tok EscBackslash s ->
    str_token_string ("""" :: tok)%bs EscNone (s ++ """")%bs.
Proof.
  inversion 1; cbn.
  rewrite string_app_assoc, escape_string_dquote, <- string_reverse_cons.
  constructor.
Qed.

Lemma str_token_string_tab tok s
  : str_token_string tok EscBackslash s ->
    str_token_string ("009" :: tok)%bs EscNone (s ++ "t")%bs.
Proof.
  inversion 1; cbn.
  rewrite string_app_assoc, escape_string_tab, <- string_reverse_cons.
  constructor.
Qed.

Lemma str_token_string_carriage_return tok s
  : str_token_string tok EscBackslash s ->
    str_token_string ("013" :: tok)%bs EscNone (s ++ "r")%bs.
Proof.
  inversion 1; cbn.
  rewrite string_app_assoc, escape_string_carriage_return, <- string_reverse_cons.
  constructor.
Qed.

Lemma str_token_string_escape tok s
  : str_token_string tok EscNone s ->
    str_token_string tok EscBackslash (s ++ "\")%bs.
Proof.
  inversion 1; cbn; constructor.
Qed.

Lemma str_token_string_regular c tok s
  : is_printable c = true \/ is_utf_8 c = true ->
    """"%byte <> c ->
    "\"%byte <> c ->
    str_token_string tok EscNone s ->
    str_token_string (c :: tok)%bs EscNone (s ++ c :: "")%bs.
Proof.
  inversion 4; cbn.
  rewrite escape_string_regular by auto.
  rewrite <- string_reverse_cons.
  constructor.
Qed.

Inductive partial_token_string : partial_token -> string -> Prop :=
| partial_token_string_NoToken
  : partial_token_string NoToken ""%bs
| partial_token_string_SimpleToken p s s'
  : atom_string s' ->
    s' = string_reverse s ->
    partial_token_string (SimpleToken p s) s'
| partial_token_string_StrToken p tok e s'
  : str_token_string tok e s' ->
    partial_token_string (StrToken p tok e) s'
| partial_token_string_Comment s
  : no_newline s ->
    partial_token_string Comment (";" :: s)%bs
.
Local Hint Constructors partial_token_string : ceres.

Inductive parser_state_string_
    (more : bool) (d : list sexp) (u : list symbol) (s0 : string) : Prop :=
| parser_state_string_mk_ ts00 ts01
  : token_string more (ts00 ++ ts01) s0 ->
    list_sexp_tokens (rev d) ts00 ->
    stack_tokens u ts01 ->
    stack_end u ->
    parser_state_string_ more d u s0
.
Local Hint Constructors parser_state_string_ : ceres.

Lemma parser_state_string_map d u more more' s0 s0'
  : (forall ts, token_string more ts s0 -> token_string more' ts s0') ->
    parser_state_string_ more  d u s0 ->
    parser_state_string_ more' d u s0'.
Proof.
  intros f []; eauto with ceres.
Qed.

(* Invariant on the parsed prefix *)
Inductive parser_state_string (i : parser_state) : string -> Prop :=
| parser_state_string_mk more s0 s1
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    more_ok more s1 ->
    partial_token_string (parser_cur_token i) s1 ->
    parser_state_string i (s0 ++ s1)%bs
.
Local Hint Constructors parser_state_string : ceres.

Lemma more_ok_atom_inv more s
  : more_ok more s ->
    atom_string s ->
    more = false.
Proof.
  intros [| c s' Hc]; auto.
  intros [_ Hs]. cbn in Hs. rewrite Hc in Hs. discriminate.
Qed.

Lemma new_sexp_Atom_sound d u s0 more
    (Hdu : parser_state_string_ more d u s0)
    (s' : string)
    (Hmore : more_ok more s')
    (s1' : string)
    (H : atom_string s')
    (H0 : s' = string_reverse s1')
    (i' := new_sexp d u (Atom (raw_or_num s1')) tt)
  : parser_state_string_ true (parser_done i') (parser_stack i') (s0 ++ s')%bs.
Proof.
  unfold new_sexp in i'.
  assert (more = false) by eauto using more_ok_atom_inv; subst more.
  destruct Hdu as [ ts00 ts01 Hs0 Hts Hstack Hend ].
  destruct u; cbn; clear i'.
  - inversion Hstack; subst ts01; clear Hstack. rewrite app_nil_r in Hs0.
    apply parser_state_string_mk_
      with (ts00 := ts00 ++ [Token.Atom s']) (ts01 := []);
      cbn; auto with ceres.
    + rewrite app_nil_r.
      auto using token_string_atom_snoc.
    + subst s'; auto using list_sexp_tokens_app, atom_token_atom with ceres.
  - apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Atom s']);
      cbn; auto with ceres.
    + rewrite app_assoc.
      auto using token_string_atom_snoc.
    + subst s'; auto using atom_token_atom with ceres.
Qed.

Lemma new_sexp_List_sound d u s0 ts00 ts01 ts02 more
    (es : list sexp)
    (Hs0 : token_string more (ts00 ++ ts01 ++ [Token.Open] ++ ts02) s0)
    (Hdone : list_sexp_tokens (rev d) ts00)
    (Hstack : stack_tokens u ts01)
    (Hstackend : stack_end u)
    (Hes : list_sexp_tokens es ts02)
  : parser_state_string (new_sexp d u (List es) NoToken) (s0 ++ ")")%bs.
Proof.
  unfold new_sexp.
  destruct u.
  - inversion Hstack; subst; clear Hstack. cbn in Hs0.
    rewrite <- (string_app_nil_r (_ ++ ")"))%bs.
    apply parser_state_string_mk with (more := false); cbn; auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00 ++ [Token.Open] ++ ts02 ++ [Token.Close]) (ts01 := []);
      cbn; auto with ceres.
    + rewrite app_nil_r.
      change (?x :: ?y ++ ?z) with ((x :: y) ++ z).
      rewrite !(app_assoc _ _ [Token.Close]).
      eauto using token_string_close_snoc.
    + apply list_sexp_tokens_app; auto.
      rewrite <- (app_nil_r (_ :: _ ++ _)).
      auto with ceres.
  - rewrite <- (string_app_nil_r (_ ++ ")"))%bs.
    econstructor; cbn; auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Open] ++ ts02 ++ [Token.Close]);
      cbn; auto with ceres.
    change (?x :: ?y ++ ?z) with ((x :: y) ++ z).
    rewrite !(app_assoc _ _ [Token.Close]).
    eauto using token_string_close_snoc.
Qed.

Lemma new_sexp_Str_sound (d : list sexp) (u : list symbol) (more : bool)
    (s0 tok s' : string)
    (Hi : parser_state_string_ more d u s0)
    (H : str_token_string tok EscNone s')
  : parser_state_string
      (new_sexp d u (Atom (Str (string_reverse tok))) NoToken)
      (s0 ++ s' ++ """")%bs.
Proof.
  rewrite <- (string_app_nil_r (_ ++ _ ++ """"))%bs.
  unfold new_sexp.
  destruct Hi. inversion_clear H.
  destruct u.
  - inversion H2; subst; clear H2.
    apply parser_state_string_mk with (more := false); cbn; auto with ceres.
    apply parser_state_string_mk_
     with (ts00 := ts00 ++ [Token.Str (string_reverse tok)]) (ts01 := []);
     cbn; auto with ceres.
    + rewrite app_nil_r in *.
      eapply token_string_string_snoc; eauto.
    + apply list_sexp_tokens_app; eauto with ceres.
  - econstructor; cbn; auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Str (string_reverse tok)]);
      cbn; auto with ceres.
    rewrite app_assoc.
    eapply token_string_string_snoc. eauto.
Qed.

Lemma _fold_stack_sound_
    d
    (p : loc)
    (s0 : string)
    (more : bool)
    u
  : forall
    (es : list sexp)
    (ts00 ts01 ts02 : list Token.t)
    (Hs0 : token_string more (ts00 ++ ts01 ++ ts02) s0)
    (Hdone : list_sexp_tokens (rev d) ts00)
    (Hstack : stack_tokens u ts01)
    (Hstackend : stack_end u)
    (Hes : list_sexp_tokens es ts02)
  , on_right (_fold_stack d p es u)
      (fun i' : parser_state => parser_state_string i' (s0 ++ ")"))%bs.
Proof.
  induction u; cbn; auto; intros.
  destruct a; cbn.
  - inversion Hstack; subst; clear Hstack.
    rewrite <- app_assoc in Hs0.
    eauto using new_sexp_List_sound with ceres.
  - inversion Hstack; subst; clear Hstack.
    rewrite <- app_assoc in Hs0.
    specialize IHu with (1 := Hs0).
    apply IHu; eauto with ceres.
Qed.

Lemma _fold_stack_sound
    d
    (p : loc)
    (s0 : string)
    (more : bool)
    u
  : parser_state_string_ more d u s0 ->
    on_right (_fold_stack d p [] u)
      (fun i' : parser_state => parser_state_string i' (s0 ++ ")"))%bs.
Proof.
  intros [ts00 ts01 ? ?]; apply _fold_stack_sound_
    with (more := more) (ts00 := ts00) (ts01 := ts01) (ts02 := []); auto with ceres.
  rewrite app_nil_r; auto with ceres.
Qed.

Lemma token_string_spaces_app more ts s c
  : is_whitespace c = true ->
    token_string more ts s ->
    token_string false ts (s ++ c :: "")%bs.
Proof.
  intros Hc; induction 1; cbn; try rewrite string_app_assoc; auto with ceres.
  - apply token_string_spaces with (ws := (c :: "")%bs); auto with ceres.
    red; cbn; rewrite Hc; auto.
  - apply token_string_atom; auto with ceres.
    eauto using after_atom_string_snoc with ceres.
Qed.

Lemma next_sound' {T} (i : parser_state_ T) (more : bool) s0 p c
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    is_atom_char c = false ->
    on_right (next' i p c) (fun i' =>
      parser_state_string i' (s0 ++ c :: ""))%bs.
Proof.
  intros [ts00 ts01 Hs0 Hdone Hstack] IAC_c.
  unfold next'; match_byte; cbn.
  + (* "(" *)
    rewrite <- (string_app_nil_r (_ ++ "("))%bs.
    apply parser_state_string_mk with (more := false); auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Open]);
      cbn; eauto with ceres.
    rewrite app_assoc; apply token_string_open_snoc with (more := more); eauto with ceres.
  + (* ")" *)
    eauto using _fold_stack_sound with ceres.
  + (* """" *)
    eapply parser_state_string_mk; cbn; eauto using str_token_string_new, more_ok_cons with ceres.
  + (* ";" *)
    eapply parser_state_string_mk; cbn; eauto using more_ok_cons with ceres.
  + (* else *)
    destruct (is_whitespace y) eqn:Ews; cbn.
    * rewrite <- (string_app_nil_r (_ ++ y :: ""))%bs.
      eauto using token_string_spaces_app with ceres.
    * auto.
Qed.

Lemma more_ok_atom more s c
  : more_ok more s ->
    atom_string s ->
    is_atom_char c = true ->
    more_ok more (s ++ c :: "")%bs.
Proof.
  intros []; cbn; auto with ceres.
Qed.
Local Hint Resolve more_ok_atom : ceres.

Lemma string_reverse_cons' c s s'
  : s' = string_reverse s ->
    (s' ++ c :: "")%bs = string_reverse (c :: s)%bs.
Proof.
  intros; subst; symmetry; apply string_reverse_cons.
Qed.

Lemma next_str_sound
    (i : parser_state) (p p1 : loc) (c : byte) (e : escape)
    (more : bool) (s0 tok s' : string)
    (Hi : parser_state_string_ more (parser_done i) (parser_stack i) s0)
    (H : str_token_string tok e s')
  : on_right (next_str i p1 tok e p c)
      (fun i' : parser_state => parser_state_string i' (s0 ++ s' ++ c :: ""))%bs.
Proof with (econstructor; cbn; eauto using more_ok_str_token with ceres).
  unfold next_str.
  destruct e, i as [d u ct].
  - match_byte; cbn; auto.
    + apply str_token_string_newline in H...
    + apply str_token_string_tab in H...
    + apply str_token_string_carriage_return in H...
    + apply str_token_string_backslash in H...
    + apply str_token_string_dquote in H...
  - match_byte; try match_match; cbn; auto.
    + apply str_token_string_escape in H...
    + eauto using new_sexp_Str_sound.
    + apply Bool.orb_true_iff in H2.
      econstructor; eauto using more_ok_str_token, str_token_string_regular.
      constructor. auto using str_token_string_regular.
Qed.

Lemma next_comment_sound
    (i : parser_state)
    (c : byte)
    (more : bool)
    (s0 : string)
    (Hi : parser_state_string_ more (parser_done i) (parser_stack i) s0)
    (Ei : parser_cur_token i = Comment)
    (s1 : string)
    (Hs : no_newline s1)
  : on_right (next_comment i c) (fun i' : parser_state =>
      parser_state_string i' (s0 ++ ";" :: s1 ++ c :: ""))%bs.
Proof.
  unfold next_comment.
  match_byte; cbn.
  - rewrite <- (string_app_nil_r (_ ++ _ :: _))%bs.
    econstructor; eauto using more_ok_cons with ceres.
    revert Hi.
    apply parser_state_string_map, token_string_comment_snoc.
  - econstructor; eauto using more_ok_cons with ceres.
    rewrite Ei; constructor.
    apply not_string_elem_app; auto.
    apply not_string_elem_singleton; assumption.
Qed.

Lemma next_sound i s p c
  : parser_state_string i s ->
    on_right (next i p c) (fun i' =>
      parser_state_string i' (s ++ c :: ""))%bs.
Proof.
  intros [more s0 s1 Hi Hmore Hcur].
  unfold next.
  remember (parser_cur_token i) as ct; symmetry in Heqct.
  destruct Hcur as [ | p1' s1' | p1 tok e | s1' Hs ].
  - (* NoToken *)
    apply more_ok_nil_inv in Hmore; subst more.
    rewrite string_app_nil_r.
    destruct (is_atom_char c) eqn:IAC_c; cbn.
    + econstructor; cbn; eauto with ceres.
    + eauto using next_sound'.
  - (* SimpleToken *)
    destruct (is_atom_char c) eqn:IAC_c; cbn.
    + rewrite string_app_assoc.
      econstructor; cbn; eauto using string_reverse_cons' with ceres.
    + destruct Hi as [ts00 ts01 Hs0 Hdone Hstack].
      eauto using next_sound', new_sexp_Atom_sound with ceres.
  - (* StrToken *)
    rewrite string_app_assoc; cbn.
    eauto using next_str_sound.
  - (* Comment *)
    rewrite string_app_assoc; cbn.
    eauto using next_comment_sound.
Qed.

Lemma _done_or_fail_sound d u
    (more : bool)
    (s0 : string)
    (H : parser_state_string_ more d u s0)
  : on_right (_done_or_fail d u)
      (fun es : list sexp =>
       exists ts : list Token.t,
         list_sexp_tokens es ts /\ token_string more ts s0).
Proof.
  destruct H.
  destruct H2 as [ | ? H2]; cbn.
  - inversion H1; subst; clear H1. rewrite app_nil_r in *.
    exists ts00. unfold rev'; rewrite <- rev_alt.
    eauto.
  - clear H1. induction H2; intros; cbn; auto.
    destruct u; cbn; auto.
Qed.

Lemma eof_sound
    (i : parser_state)
    (p : loc)
    (s : string)
    (H : parser_state_string i s)
  : on_right (eof i p) (fun es : list sexp =>
      exists (ts : list Token.t),
        list_sexp_tokens es ts /\ token_string false ts (s ++ newline))%bs.
Proof.
  unfold eof.
  destruct H as [ more s0 s1 H Hmore Hpartial ].
  destruct Hpartial; cbn; auto.
  - rewrite string_app_nil_r.
    eauto using _done_or_fail_sound, parser_state_string_map, token_string_newline_snoc.
  - eauto using _done_or_fail_sound, new_sexp_Atom_sound, parser_state_string_map, token_string_newline_snoc.
  - rewrite string_app_assoc. eapply _done_or_fail_sound. cbn.
    revert H.
    apply parser_state_string_map, token_string_comment_snoc.
Qed.

Lemma _parse_sexps_sound i p (s0 s : string)
  : parser_state_string i s0 ->
    match parse_sexps_ i p s with
    | (None, p', i') =>
      on_right (eof i' p') (fun es =>
        exists ts,
          list_sexp_tokens es ts /\ token_string false ts (s0 ++ s ++ newline))%bs
    | (Some _, _, _) => True
    end.
Proof.
  revert i p s0; induction s as [ | c s ]; intros; cbn.
  - apply eof_sound; auto.
  - pose proof next_sound as SOUND.
    specialize (SOUND i s0 p c H).
    destruct next as [ | i']; auto; cbn in SOUND.
    specialize (IHs i' (N.succ p) _ SOUND).
    destruct parse_sexps_ as [ [ [ | ] ] ? ]; auto.
    destruct eof; auto; cbn in *.
    destruct IHs as (ts & Hts & Hs0).
    rewrite string_app_assoc in Hs0.
    eauto.
Qed.

Lemma parser_state_empty : parser_state_string initial_state ""%bs.
Proof.
  change ""%bs with ("" ++ "")%bs.
  repeat econstructor; cbn; auto with ceres.
Qed.

(* If the parser succeeds, then the expressions relate to the input string. *)
Theorem parse_sexps_sound : PARSE_SEXPS_SOUND.
Proof.
  red; intros.
  unfold parse_sexps.
  pose proof (_parse_sexps_sound initial_state 0%N ""%bs s parser_state_empty) as SOUND.
  destruct parse_sexps_ as [ [ [ | ] ] ? ]; cbn; auto.
Qed.
