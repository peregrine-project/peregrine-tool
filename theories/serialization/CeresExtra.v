From Stdlib Require Import List.
From Ceres Require Import Ceres.
From Ceres Require Import CeresUtils.
From Ceres Require CeresParserUtils.
From Ceres Require CeresString.
From MetaRocq.Utils Require Import bytestring.
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



Local Open Scope bs_scope.

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
  CeresString.eqb_byte c c = true.
Proof.
  intros c.
  destruct c; reflexivity.
Qed.

Lemma neqb_ascii_neq : forall a b,
  a <> b -> CeresString.eqb_byte a b = false.
Proof.
  intros.
  apply CeresString.neqb_neq_byte.
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
    _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a)%list.
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

(** ** Soundness lemma for lists from Forall *)

(** This lemma allows proving list soundness when we have individual soundness
    proofs for each element via a Forall predicate (from structural induction)
    rather than a SoundClass instance. *)
Lemma sound_list_from_forall {A : Type} (ser : A -> sexp) (des : FromSexp A) (es : list sexp) :
  forall xs n l ts,
    Forall (fun e => forall l' t, des l' e = inr t -> ser t = e) es ->
    _sexp_to_list des xs n l es = inr ts ->
    map ser ts = (map ser (rev xs) ++ es)%list.
Proof.
  induction es as [| e es' IHes]; intros xs n l ts Hforall Hdeser.
  - (* Base case: empty list *)
    cbn in Hdeser.
    injection Hdeser as <-.
    rewrite rev_alt, app_nil_r.
    reflexivity.
  - (* Inductive case: e :: es' *)
    cbn in Hdeser.
    destruct (des (n :: l) e) as [err | t] eqn:Hdes_e; [discriminate|].
    (* Apply IH with extended accumulator *)
    specialize (IHes (t :: xs) (S n) l ts).
    inversion Hforall as [|e' es'' He Hes' Heq1 Heq2]; subst.
    apply IHes in Hdeser; [|assumption].
    (* Now Hdeser : map ser ts = map ser (rev (t :: xs)) ++ es' *)
    rewrite Hdeser.
    cbn [rev].
    rewrite map_app. cbn [map].
    (* Need: map ser (rev xs) ++ [ser t] ++ es' = map ser (rev xs) ++ e :: es' *)
    (* Since He : forall l' t, des l' e = inr t -> ser t = e *)
    (* and Hdes_e : des (n :: l) e = inr t, we have ser t = e *)
    specialize (He (n :: l) t Hdes_e).
    rewrite He.
    rewrite <- app_assoc. cbn.
    reflexivity.
Qed.

(** Specialized version for soundness proofs: if deserialization of a sexp list
    succeeds and each sexp satisfies soundness, then the serialized result
    equals the original sexp list. *)
Corollary sound_list_from_forall_nil {A : Type} (ser : A -> sexp) (des : FromSexp A) (es : list sexp) :
  forall l ts,
    Forall (fun e => forall l' t, des l' e = inr t -> ser t = e) es ->
    _sexp_to_list des nil 0 l es = inr ts ->
    map ser ts = es.
Proof.
  intros l ts Hforall Hdeser.
  apply sound_list_from_forall with (xs := nil) (n := 0) (l := l) in Hforall; [|assumption].
  cbn in Hforall.
  assumption.
Qed.

(** ** Strong soundness with nested Forall access *)

(** For term serialization, we need access to nested Foralls when an element
    of a list is itself a List sexp. This definition captures both the
    soundness property AND provides access to nested structure. *)

Inductive StrongSound (P : sexp -> Prop) : sexp -> Prop :=
| SS_Atom : forall a, P (Atom a) -> StrongSound P (Atom a)
| SS_List : forall es,
    P (List es) ->
    Forall (StrongSound P) es ->
    StrongSound P (List es).

(** StrongSound implies the underlying property *)
Lemma StrongSound_implies_P {P : sexp -> Prop} : forall e,
  StrongSound P e -> P e.
Proof.
  intros e Hss. destruct Hss; assumption.
Qed.

(** For a List sexp, we can extract the nested Forall *)
Lemma StrongSound_List_inv {P : sexp -> Prop} : forall es,
  StrongSound P (List es) -> Forall (StrongSound P) es.
Proof.
  intros es Hss. inversion Hss; assumption.
Qed.

(** Build StrongSound from sexp structural induction *)
Lemma StrongSound_from_sexp_ind (P : sexp -> Prop) :
  (forall a, P (Atom a)) ->
  (forall es, Forall P es -> P (List es)) ->
  forall e, StrongSound P e.
Proof.
  intros Hatom Hlist.
  apply CeresS.sexp__ind with (Pl := fun es => Forall (StrongSound P) es).
  - (* Atom case *)
    intros a. apply SS_Atom. apply Hatom.
  - (* List case *)
    intros es Hforall_ss.
    apply SS_List.
    + apply Hlist.
      clear Hlist.
      induction Hforall_ss as [| e es' Hss Hforall_ss' IH].
      * constructor.
      * constructor.
        -- apply StrongSound_implies_P. assumption.
        -- assumption.
    + assumption.
  - (* nil case *)
    constructor.
  - (* cons case *)
    intros e es Hss Hforall_ss.
    constructor; assumption.
Qed.

(** Extract Forall P from Forall (StrongSound P) *)
Lemma Forall_StrongSound_to_Forall_P {P : sexp -> Prop} : forall es,
  Forall (StrongSound P) es -> Forall P es.
Proof.
  intros es Hss.
  induction Hss as [| e es' Hss_e Hss_es' IH].
  - constructor.
  - constructor.
    + apply StrongSound_implies_P. assumption.
    + assumption.
Qed.

(** Key lemma: when we have StrongSound for a List element, we get Forall for its contents *)
Lemma StrongSound_List_extract_forall {P : sexp -> Prop} : forall es,
  StrongSound P (List es) ->
  Forall P es.
Proof.
  intros es Hss.
  apply Forall_StrongSound_to_Forall_P.
  apply StrongSound_List_inv.
  assumption.
Qed.

(** For products where second component uses custom deserializer:
    If we have StrongSound P for each product sexp (List [a_sexp; b_sexp])
    and the second sexp satisfies P, then the product list deserializes soundly.

    The key is that StrongSound gives us access to the NESTED elements. *)
Lemma sound_prod_list_from_strong {A B : Type}
      (serA : A -> sexp) (desA : FromSexp A)
      (serB : B -> sexp) (desB : FromSexp B)
      {HSA : SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' t, desB l' e = inr t -> serB t = e) :
  forall es,
    Forall (StrongSound P) es ->
    forall xs n l ts,
      _sexp_to_list (Deserialize_prod desA desB) xs n l es = inr ts ->
      map (fun p => List [serA (fst p); serB (snd p)]) ts =
      (map (fun p => List [serA (fst p); serB (snd p)]) (rev xs) ++ es)%list.
Proof.
  induction es as [| e es' IHes]; intros Hss xs n l ts Hdeser.
  - (* Base case: empty list *)
    cbn in Hdeser.
    injection Hdeser as <-.
    rewrite rev_alt, app_nil_r.
    reflexivity.
  - (* Inductive case *)
    cbn in Hdeser.
    destruct e as [a | elems]; [discriminate|].
    destruct elems as [|e1 [|e2 [|]]]; try discriminate.
    destruct (desA (0 :: n :: l) e1) as [err|a] eqn:Hdes_a; [discriminate|].
    destruct (desB (1 :: n :: l) e2) as [err|b] eqn:Hdes_b; [discriminate|].
    (* Extract StrongSound for this element and the rest *)
    inversion Hss as [|e' es'' Hss_e Hss_es' Heq1 Heq2]; subst.
    (* Hss_e : StrongSound P (List [e1; e2]) *)
    (* From StrongSound, extract P for e2 *)
    inversion Hss_e as [|elems' HP_list Hss_inner Heq3]; subst.
    (* Hss_inner : Forall (StrongSound P) [e1; e2] *)
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_e2 _].
    (* Hss_e2 : StrongSound P e2 *)
    apply StrongSound_implies_P in Hss_e2.
    (* Hss_e2 : P e2 *)
    specialize (IHes Hss_es' ((a, b) :: xs) (S n) l ts Hdeser).
    rewrite IHes.
    cbn [rev map].
    rewrite map_app. cbn [map].
    rewrite <- app_assoc. cbn.
    f_equal. f_equal. f_equal.
    + apply sound_class in Hdes_a. assumption.
    + apply HP in Hss_e2. apply Hss_e2. assumption.
Qed.

(** Corollary for soundness with nil accumulator *)
Corollary sound_prod_list_from_strong_nil {A B : Type}
      (serA : A -> sexp) (desA : FromSexp A)
      (serB : B -> sexp) (desB : FromSexp B)
      {HSA : SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' t, desB l' e = inr t -> serB t = e) :
  forall es l ts,
    Forall (StrongSound P) es ->
    _sexp_to_list (Deserialize_prod desA desB) nil 0 l es = inr ts ->
    map (fun p => List [serA (fst p); serB (snd p)]) ts = es.
Proof.
  intros es l ts Hss Hdeser.
  apply (sound_prod_list_from_strong serA desA serB desB HSA P HP es Hss nil 0 l ts) in Hdeser.
  cbn in Hdeser. assumption.
Qed.

(** For def list: extract soundness when we have StrongSound for def sexps
    Each def sexp is: List [Atom "def"; name_sexp; body_sexp; rarg_sexp]
    The body_sexp satisfies P, which gives soundness for the body *)
Lemma sound_def_list_from_strong {T : Set}
      (serT : T -> sexp) (desT : FromSexp T)
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' t, desT l' e = inr t -> serT t = e) :
  forall es,
    Forall (StrongSound P) es ->
    forall xs n l (ts : list (def T)),
      _sexp_to_list (@_from_sexp (def T) (@Deserialize_def T desT)) xs n l es = inr ts ->
      map to_sexp ts = (map to_sexp (rev xs) ++ es)%list.
Proof.
  induction es as [| e es' IHes]; intros Hss xs n l ts Hdeser.
  - (* Base case *)
    cbn in Hdeser.
    injection Hdeser as <-.
    rewrite rev_alt, app_nil_r.
    reflexivity.
  - (* Inductive case *)
    inversion Hss as [|e' es'' Hss_e Hss_es' Heq1 Heq2]; subst.
    cbn in Hdeser.
    (* Unfold def deserialization *)
    unfold _from_sexp, Deserialize_def in Hdeser.
    apply sound_match_con in Hdeser.
    destruct Hdeser as [Hdeser | Hdeser]; elim_Exists Hdeser.
    destruct Hdeser as [fields [Heq Hfields]].
    cbn in Heq; inversion Heq; subst; clear Heq.
    (* sound_field gives us the field deserializations *)
    sound_field Hfields.
    (* Ea0 : name, Ea1 : body, Ea2 : rarg *)
    apply sound_class in Ea0.
    apply sound_class in Ea2.
    (* For Ea1 (body), we need to use HP via StrongSound *)
    (* Hss_e : StrongSound P (List [Atom "def"; name_sexp; body_sexp; rarg_sexp]) *)
    inversion Hss_e as [|fields' HP_list Hss_inner Heq3]; subst.
    (* Hss_inner : Forall (StrongSound P) [Atom "def"; name_sexp; body_sexp; rarg_sexp] *)
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_body _].
    apply StrongSound_implies_P in Hss_body.
    apply HP in Hss_body.
    specialize (Hss_body _ _ Ea1).
    (* Now apply IH *)
    specialize (IHes Hss_es' ({| dname := a0; dbody := a1; rarg := a2 |} :: xs) (S n) l ts Hdeser0).
    rewrite IHes.
    cbn [rev map to_sexp Serialize_def].
    rewrite map_app. cbn [map].
    rewrite <- app_assoc. cbn.
    f_equal. f_equal. f_equal.
    + rewrite Ea0. reflexivity.
    + assumption.
    + rewrite Ea2. reflexivity.
Qed.

(** Corollary for def list with nil accumulator *)
Corollary sound_def_list_from_strong_nil {T : Set}
      (serT : T -> sexp) (desT : FromSexp T)
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' t, desT l' e = inr t -> serT t = e) :
  forall es l (ts : list (def T)),
    Forall (StrongSound P) es ->
    _sexp_to_list (@_from_sexp (def T) (@Deserialize_def T desT)) nil 0 l es = inr ts ->
    map to_sexp ts = es.
Proof.
  intros es l ts Hss Hdeser.
  apply (sound_def_list_from_strong serT desT P HP es Hss nil 0 l ts) in Hdeser.
  cbn in Hdeser. assumption.
Qed.

(** For prim_val soundness when we have P for the inner type
    This handles the recursive case where we don't have SoundClass yet.

    The prim_val sexp is: List [tag_sexp; value_sexp]
    - For primInt/Float/String: value_sexp doesn't contain T
    - For primArray: value_sexp = List [Atom "array_model"; default_sexp; values_sexp]
      where both default_sexp and each element in values_sexp needs P
*)
Lemma sound_prim_val_from_strong {T : Set}
      (serT : T -> sexp) (desT : FromSexp T)
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' t, desT l' e = inr t -> serT t = e) :
  forall e l (p : EPrimitive.prim_val T),
    StrongSound P e ->
    @_from_sexp (EPrimitive.prim_val T) (@Deserialize_prim_val T desT) l e = inr p ->
    @to_sexp (EPrimitive.prim_val T) (@Serialize_prim_val T serT) p = e.
Proof.
  intros e l p Hss Hdes.
  destruct e; cbn in *; try discriminate.
  destruct xs as [|tag_sexp [|val_sexp [|]]]; try discriminate.
  destruct (_from_sexp l tag_sexp) as [err|tag] eqn:Htag; try discriminate.
  apply sound_class in Htag.
  destruct tag.
  - (* primInt *)
    destruct (_from_sexp l val_sexp) as [err|i] eqn:Hval; try discriminate.
    apply sound_class in Hval.
    injection Hdes as <-.
    cbn. rewrite <- Htag, <- Hval. reflexivity.
  - (* primFloat *)
    destruct (_from_sexp l val_sexp) as [err|f] eqn:Hval; try discriminate.
    apply sound_class in Hval.
    injection Hdes as <-.
    cbn. rewrite <- Htag, <- Hval. reflexivity.
  - (* primString *)
    destruct (_from_sexp l val_sexp) as [err|s] eqn:Hval; try discriminate.
    apply sound_class in Hval.
    injection Hdes as <-.
    cbn. rewrite <- Htag, <- Hval. reflexivity.
  - (* primArray - this case needs P for the inner terms *)
    destruct (_from_sexp l val_sexp) as [err|arr] eqn:Hval; try discriminate.
    injection Hdes as <-.
    (* Hss : StrongSound P (List [tag_sexp; val_sexp]) *)
    (* Need to extract soundness for the array *)
    inversion Hss as [|fields HP_list Hss_inner Heq]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_val _].
    (* Hss_val : StrongSound P val_sexp *)
    (* val_sexp should be List [Atom "array_model"; default_sexp; values_sexp] *)
    destruct val_sexp as [a | fields]; cbn in Hval; try discriminate.
    apply sound_match_con in Hval.
    destruct Hval as [Hval | Hval]; elim_Exists Hval.
    destruct Hval as [fields' [Heq' Hfields']].
    cbn in Heq'; inversion Heq'; subst; clear Heq'.
    sound_field Hfields'.
    (* Ea0 : default, Ea1 : values list *)
    (* Need to show soundness using P *)
    inversion Hss_val as [|fields'' HP_val Hss_val_inner Heq'']; subst.
    apply List.Forall_cons_iff in Hss_val_inner as [_ Hss_val_inner].
    apply List.Forall_cons_iff in Hss_val_inner as [Hss_default Hss_val_inner].
    apply List.Forall_cons_iff in Hss_val_inner as [Hss_values _].
    apply StrongSound_implies_P in Hss_default.
    apply HP in Hss_default.
    specialize (Hss_default _ _ Ea0).
    (* For values list *)
    destruct e1; cbn in Ea1; try discriminate.
    apply StrongSound_List_inv in Hss_values.
    apply sound_list_from_forall with (xs := nil) (n := 0) (l := 1 :: l) in Ea1.
    + cbn in Ea1.
      cbn. rewrite <- Htag, Hss_default.
      unfold to_sexp, Serialize_array_model. cbn.
      rewrite Ea1. reflexivity.
    + clear Ea1.
      apply Forall_StrongSound_to_Forall_P in Hss_values.
      eapply List.Forall_impl. 2: apply Hss_values.
      intros e' He' l' t' Hdes'.
      apply HP. assumption. assumption.
Qed.
