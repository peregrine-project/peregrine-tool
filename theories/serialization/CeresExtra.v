From Stdlib Require Import String.
From Stdlib Require Import List.
From Ceres Require Import Ceres.
From Ceres Require Import CeresUtils.
From Ceres Require CeresParserUtils.
From Ceres Require CeresString.
From MetaRocq.Utils Require bytestring.
From MetaRocq.Utils Require All_Forall.

Local Notation "p >>= f" := (Deser.bind_field p f) (at level 50, left associativity) : deser_scope.
Local Open Scope deser_scope.



Definition con6 {A B C D E F R} (f : A -> B -> C -> D -> E -> F -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexpList R :=
  fun pa pb pc pd pe pf =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' =>
    Deser.ret (f a b c d e f')).

Definition con6_ {A B C D E F R} (f : A -> B -> C -> D -> E -> F -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F}
  : FromSexpList R :=
  con6 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con7 {A B C D E F G R} (f : A -> B -> C -> D -> E -> F -> G -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexpList R :=
  fun pa pb pc pd pe pf pg =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g =>
    Deser.ret (f a b c d e f' g)).

Definition con7_ {A B C D E F G R} (f : A -> B -> C -> D -> E -> F -> G -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G}
  : FromSexpList R :=
  con7 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con8 {A B C D E F G H R} (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h =>
    Deser.ret (f a b c d e f' g h)).

Definition con8_ {A B C D E F G H R} (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H}
  : FromSexpList R :=
  con8 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con9 {A B C D E F G H I R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i =>
    Deser.ret (f a b c d e f' g h i)).

Definition con9_ {A B C D E F G H I R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I}
  : FromSexpList R :=
  con9 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con10 {A B C D E F G H I J R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
    Deser.ret (f a b c d e f' g h i j)).

Definition con10_ {A B C D E F G H I J R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  : FromSexpList R :=
  con10 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.



Definition string_of_loc (l : loc) : string := CeresString.comma_sep (map CeresString.string_of_nat l).

Fixpoint string_of_message (print_sexp : bool) (m : message) : string :=
  match m with
  | MsgStr s => s
  | MsgSexp e => if print_sexp then string_of_sexp e else ""
  | MsgApp m1 m2 =>
    let m1_str := string_of_message print_sexp m1 in
    let m2_str := string_of_message print_sexp m2 in
    m1_str ++ m2_str
  end.

Definition string_of_error (print_loc print_sexp : bool) (e : error) : string :=
  match e with
  (* Errors from parsing [string -> sexp] *)
  | ParseError e => CeresParserUtils.pretty_error e
  (* Errors from deserializing [sexp -> A] *)
  | DeserError l m =>
    let msg_str := string_of_message print_sexp m in
    if print_loc
    then msg_str ++ " at location " ++ string_of_loc l
    else msg_str
  end.



Lemma eqb_ascii_refl : forall c,
  CeresString.eqb_ascii c c = true.
Proof.
  intros c.
  destruct c.
  unfold CeresString.eqb_ascii.
  rewrite !Bool.eqb_reflx.
  reflexivity.
Qed.

Lemma neqb_ascii_neq : forall a b,
  a <> b -> CeresString.eqb_ascii a b = false.
Proof.
  intros.
  apply CeresString.neqb_neq_ascii.
  assumption.
Qed.

Lemma bytestring_complete : forall s,
  bytestring.String.of_string (bytestring.String.to_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.byte_of_ascii_of_byte.
    reflexivity.
Qed.

Lemma bytestring_sound : forall s,
  bytestring.String.to_string (bytestring.String.of_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.ascii_of_byte_of_ascii.
    reflexivity.
Qed.

Lemma complete_class_list_all {A : Type} {H : Serialize A} {H0 : Deserialize A} :
  forall (a xs : list A) (n : nat) (l : loc),
    All_Forall.All
      (fun t : A =>
       forall l : loc, _from_sexp l (to_sexp t) = inr t) a ->
    _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a).
Proof.
  induction a; intros; cbn.
  - rewrite rev_alt, app_nil_r.
    reflexivity.
  - inversion X; subst.
    rewrite H2.
    rewrite app_cons_assoc.
    apply IHa.
    assumption.
Qed.

Lemma complete_class_all_prod {A B : Type} {H : Serialize A} {H0 : Deserialize A} {H1 : Serialize B} {H2 : Deserialize B} :
  forall xs,
    CompleteClass A ->
    All_Forall.All
      (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp (snd x)) = inr (snd x)) xs ->
      All_Forall.All
        (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp x) = inr x) xs.
Proof.
  induction xs; intros.
  - apply All_Forall.All_nil.
  - apply All_Forall.All_cons.
    + intros.
      inversion X; subst.
      cbn.
      rewrite H5.
      rewrite complete_class.
      destruct a; cbn.
      reflexivity.
    + inversion X; subst.
      apply IHxs; assumption.
Qed.
