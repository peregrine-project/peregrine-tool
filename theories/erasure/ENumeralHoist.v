(** * Hoisting large numerals into global constants

    A numeral of [BinNums] ([positive], [N], [Z]) is, in lambda-box, a chain
    of constructor applications, one per bit.  The C backend compiles such a
    chain into code whose size, and whose compile time and memory, grow with
    the number of bits: a program with a few 2048-bit numerals does not
    compile in 4 GB.  When the numeric types are remapped to a big-integer
    library, the chain is also rebuilt at run time, one constructor call per
    bit.

    This pass moves every closed numeral of at least [th] bits into a fresh
    global constant whose body is that numeral, and replaces the numeral by a
    reference to the constant.  The constants live in the module path
    [PeregrineNumerals]; their names determine their values, so a backend can
    remap each of them to a literal of its own number representation (see
    [Pipeline.numeral_remaps]).  The pass changes no other declaration.

    The constants are inserted into the environment directly above the
    newest of the [positive] and [Z] inductives, and only the declarations
    above that point
    and the main term are rewritten, so that every constant is declared
    before (below) its uses and after the inductives it mentions.

    The pass is validated: [hoist_program] checks that the new names are
    fresh and distinct, that the constant bodies are well-formed numerals of
    the environment below them, and that unfolding the constants in the
    rewritten program gives back the original program ([unlit]).  When a
    check fails the pass is the identity.  [hoist_numerals_transformation]
    packages the pass as a [Transform.t]: it preserves well-formedness and
    eta-expansion, and evaluation, up to unfolding the constants in the
    value ([unlit]). *)

From Stdlib Require Import Utf8 Program ZArith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction EGlobalEnv
  ELiftSubst EWellformed EWcbvEval ECSubst EReflect EProgram EEtaExpandedFix.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure Require EExtends.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Import bytestring.
Import MetaRocq.Common.Transform.Transform.
Local Open Scope bs_scope.

(** ** Numerals *)

Definition binnums : modpath := MPfile ["BinNums"; "Numbers"; "Corelib"].
Definition ind_pos : inductive := mkInd (binnums, "positive") 0.
Definition ind_N : inductive := mkInd (binnums, "N") 0.
Definition ind_Z : inductive := mkInd (binnums, "Z") 0.

(** The value of a closed [positive] numeral: [xI] is constructor 0, [xO]
    constructor 1 and [xH] constructor 2. *)
Fixpoint pos_of_term (t : term) : option positive :=
  match t with
  | tConstruct i 2 [] => if i == ind_pos then Some xH else None
  | tApp (tConstruct i 0 []) a =>
      if i == ind_pos then option_map xI (pos_of_term a) else None
  | tApp (tConstruct i 1 []) a =>
      if i == ind_pos then option_map xO (pos_of_term a) else None
  | _ => None
  end.

(** The type tag and value of a closed numeral of [positive], [N] or [Z]
    ([Zpos] and [Npos] are constructor 1, [Zneg] constructor 2). *)
Definition numeral_of_term (t : term) : option (ident * Z) :=
  match pos_of_term t with
  | Some p => Some ("P", Zpos p)
  | None =>
    match t with
    | tApp (tConstruct i 1 []) a =>
        if i == ind_Z then option_map (fun p => ("Z", Zpos p)) (pos_of_term a)
        else if i == ind_N then option_map (fun p => ("N", Zpos p)) (pos_of_term a)
        else None
    | tApp (tConstruct i 2 []) a =>
        if i == ind_Z then option_map (fun p => ("Z", Zneg p)) (pos_of_term a)
        else None
    | _ => None
    end
  end.

(** A numeral is hoisted when its absolute value has at least [th] bits.
    [th = 0] disables the pass. *)
Definition big (th : nat) (t : term) : bool :=
  match numeral_of_term t with
  | Some (_, z) => (0 <? th) && (th <=? Pos.to_nat (Pos.size (Z.to_pos (Z.abs z))))
  | None => false
  end.

(** ** Names of the hoisted constants *)

Definition numerals_mp : modpath := MPfile ["PeregrineNumerals"].

(** The name of the constant of a numeral: [lit] followed by the type tag,
    [n] for a negative value, an underscore and the decimal digits of the
    absolute value, e.g. [litZn_1234] for the [Z] numeral -1234. *)
Definition lit_ident (tag : ident) (z : Z) : ident :=
  "lit" ++ tag ++ (if (z <? 0)%Z then "n" else "") ++ "_"
    ++ MRString.string_of_positive (Z.to_pos (Z.abs z)).

Definition lit_name (t : term) : kername :=
  match numeral_of_term t with
  | Some (tag, z) => (numerals_mp, lit_ident tag z)
  | None => (numerals_mp, "lit")
  end.

Definition is_lit_name (kn : kername) : bool := eqb kn (numerals_mp, kn.2).

Local Close Scope bs_scope.
Local Open Scope list_scope.

(** ** The rewriting *)

(** [hoist ok] replaces every subterm [t] with [ok t] by [tConst (lit_name t)];
    [hoist_program_table] uses for [ok] "a numeral of at least [th] bits that
    is well-formed below the insertion point". *)
Section Hoist.
  Context (ok : term -> bool).

  Fixpoint hoist (t : term) : term :=
    if ok t then tConst (lit_name t) else
    match t with
    | tEvar n l => tEvar n (map hoist l)
    | tLambda na b => tLambda na (hoist b)
    | tLetIn na b c => tLetIn na (hoist b) (hoist c)
    | tApp u v => tApp (hoist u) (hoist v)
    | tConstruct i n args => tConstruct i n (map hoist args)
    | tCase ind c brs => tCase ind (hoist c) (map (on_snd hoist) brs)
    | tProj p c => tProj p (hoist c)
    | tFix mfix idx => tFix (map (map_def hoist) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def hoist) mfix) idx
    | tPrim p => tPrim (map_prim hoist p)
    | tLazy u => tLazy (hoist u)
    | tForce u => tForce (hoist u)
    | tBox | tRel _ | tVar _ | tConst _ => t
    end.

  (** The hoisted numerals of a term, in the order [hoist] meets them. *)
  Fixpoint collect (t : term) : list term :=
    if ok t then [t] else
    match t with
    | tEvar _ l => concat (map collect l)
    | tLambda _ b => collect b
    | tLetIn _ b c => collect b ++ collect c
    | tApp u v => collect u ++ collect v
    | tConstruct _ _ args => concat (map collect args)
    | tCase _ c brs => collect c ++ concat (map (fun br => collect br.2) brs)
    | tProj _ c => collect c
    | tFix mfix _ | tCoFix mfix _ => concat (map (fun d => collect d.(dbody)) mfix)
    | tPrim p => match p.π2 with
                 | primArrayModel a => collect a.(array_default) ++ concat (map collect a.(array_value))
                 | _ => []
                 end
    | tLazy u | tForce u => collect u
    | tBox | tRel _ | tVar _ | tConst _ => []
    end.

  Definition hoist_decl (d : global_decl) : global_decl :=
    match d with
    | ConstantDecl cb => ConstantDecl {| cst_body := option_map hoist cb.(cst_body) |}
    | InductiveDecl _ => d
    end.

  Definition collect_decl (d : global_decl) : list term :=
    match d with
    | ConstantDecl {| cst_body := Some b |} => collect b
    | _ => []
    end.

End Hoist.

(** ** Unfolding the hoisted constants *)

Definition lit_table := list (kername × term).

Definition lit_lookup (L : lit_table) (kn : kername) : option term :=
  option_map snd (find (fun p => eqb p.1 kn) L).

Fixpoint unlit (L : lit_table) (t : term) : term :=
  match t with
  | tConst kn => match lit_lookup L kn with Some s => s | None => t end
  | tEvar n l => tEvar n (map (unlit L) l)
  | tLambda na b => tLambda na (unlit L b)
  | tLetIn na b c => tLetIn na (unlit L b) (unlit L c)
  | tApp u v => tApp (unlit L u) (unlit L v)
  | tConstruct i n args => tConstruct i n (map (unlit L) args)
  | tCase ind c brs => tCase ind (unlit L c) (map (on_snd (unlit L)) brs)
  | tProj p c => tProj p (unlit L c)
  | tFix mfix idx => tFix (map (map_def (unlit L)) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def (unlit L)) mfix) idx
  | tPrim p => tPrim (map_prim (unlit L) p)
  | tLazy u => tLazy (unlit L u)
  | tForce u => tForce (unlit L u)
  | tBox | tRel _ | tVar _ => t
  end.

Definition unlit_decl (L : lit_table) (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cb => ConstantDecl {| cst_body := option_map (unlit L) cb.(cst_body) |}
  | InductiveDecl _ => d
  end.

(** ** The program transformation *)

(** The constants are inserted above the newest of the inductives [positive]
    and [Z]; numerals that mention an inductive above that point (an [N]
    numeral when [N] is newer) are left in place. *)
Definition is_binnums (kn : kername) : bool :=
  eqb kn ind_pos.(inductive_mind) || eqb kn ind_Z.(inductive_mind).

(** Split an environment (newest declaration first) above its newest
    [positive] or [Z] inductive. *)
Fixpoint split_binnums (Σ : global_declarations) : option (global_declarations × global_declarations) :=
  match Σ with
  | [] => None
  | (kn, d) :: Σ' =>
      if is_binnums kn then Some ([], Σ)
      else option_map (fun '(a, b) => ((kn, d) :: a, b)) (split_binnums Σ')
  end.

(** Remove later duplicates by name. *)
Fixpoint dedup_names (seen : list kername) (l : lit_table) : lit_table :=
  match l with
  | [] => []
  | (kn, s) :: l' =>
      if existsb (eqb kn) seen then dedup_names seen l'
      else (kn, s) :: dedup_names (kn :: seen) l'
  end.

Definition lit_decl (p : kername × term) : kername × global_decl :=
  (p.1, ConstantDecl {| cst_body := Some p.2 |}).

(** A numeral is well-formed below the hoisting point when every
    constructor in it is declared there with the arity it is applied to,
    and its inductive has no parameters. *)
Fixpoint numeral_ok (Σ : global_declarations) (t : term) : bool :=
  match t with
  | tConstruct i c [] =>
      match lookup_constructor Σ i c with
      | Some (mdecl, _, cdecl) => (mdecl.(ind_npars) == 0) && (cdecl.(cstr_nargs) == 0)
      | None => false
      end
  | tApp (tConstruct i c []) a =>
      match lookup_constructor Σ i c with
      | Some (mdecl, _, cdecl) => (mdecl.(ind_npars) == 0) && (cdecl.(cstr_nargs) == 1)
                                  && numeral_ok Σ a
      | None => false
      end
  | _ => false
  end.

Fixpoint nodup_kernames (l : list kername) : bool :=
  match l with
  | [] => true
  | kn :: l' => negb (existsb (eqb kn) l') && nodup_kernames l'
  end.

Definition hoist_check (Σ newer older : global_declarations) (t : term)
  (newer' : global_declarations) (t' : term) (L : lit_table) : bool :=
  forallb (fun p => negb (isSome (lookup_env Σ p.1)) && numeral_ok older p.2
                    && isSome (numeral_of_term p.2)) L
  && nodup_kernames (map fst L)
  && (unlit L t' == t)
  && forallb2 (fun d' d => (d'.1 == d.1) && (unlit_decl L d'.2 == d.2)) newer' newer.

(** The rewritten program and its table of hoisted constants; the table is
    empty when the pass is the identity. *)
Definition hoist_program_table (th : nat) (p : eprogram) : eprogram × lit_table :=
  match split_binnums p.1 with
  | None => (p, [])
  | Some (newer, older) =>
      let ok t := big th t && numeral_ok older t in
      let newer' := map (on_snd (hoist_decl ok)) newer in
      let t' := hoist ok p.2 in
      let found := concat (map (fun d => collect_decl ok d.2) newer) ++ collect ok p.2 in
      let L := dedup_names [] (map (fun s => (lit_name s, s)) found) in
      if hoist_check p.1 newer older p.2 newer' t' L
      then ((newer' ++ map lit_decl L ++ older, t'), L)
      else (p, [])
  end.

Definition hoist_program (th : nat) (p : eprogram) : eprogram :=
  (hoist_program_table th p).1.

(** ** Syntactic properties of [unlit] *)

Section UnlitSyntax.
  Context (L : lit_table).
  Context (Hcl : forall kn s, lit_lookup L kn = Some s -> closedn 0 s).

  Lemma unlit_mkApps f args : unlit L (mkApps f args) = mkApps (unlit L f) (map (unlit L) args).
  Proof using Type. induction args in f |- *; cbn; auto. Qed.

  Lemma unlit_csubst a k b : unlit L (csubst a k b) = csubst (unlit L a) k (unlit L b).
  Proof using Hcl.
    induction b in k |- * using term_forall_list_ind; cbn;
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?length_map;
      try solve [f_equal; eauto; solve_all].
    all: try solve [destruct (Nat.compare k n); reflexivity].
    all: try solve [destruct (lit_lookup L s) eqn:E; cbn; auto;
      rewrite csubst_closed //; eapply closed_upwards; [now eapply Hcl|lia]].
    all: try solve [f_equal; eauto; solve_all; unfold on_snd; cbn; f_equal; eauto].
    all: try solve [f_equal; solve_all; unfold map_def; cbn; f_equal; rewrite length_map; eauto].
    all: try solve [f_equal; destruct p as [? []]; cbn in *; auto; depelim X; destruct p as [hd hv];
      rewrite /map_array_model; cbn; f_equal; f_equal; eauto; solve_all].
  Qed.

  Lemma unlit_substl s t : unlit L (substl s t) = substl (map (unlit L) s) (unlit L t).
  Proof using Hcl.
    induction s in t |- *; cbn; auto. rewrite IHs unlit_csubst //.
  Qed.

  Lemma unlit_iota_red pars args br :
    unlit L (iota_red pars args br) = iota_red pars (map (unlit L) args) (on_snd (unlit L) br).
  Proof using Hcl.
    rewrite /iota_red unlit_substl map_rev map_skipn //.
  Qed.

  Lemma unlit_fix_subst mfix : fix_subst (map (map_def (unlit L)) mfix) = map (unlit L) (fix_subst mfix).
  Proof using Type.
    unfold fix_subst. rewrite length_map. generalize #|mfix|.
    induction n; cbn; auto. now f_equal.
  Qed.

  Lemma unlit_cofix_subst mfix : cofix_subst (map (map_def (unlit L)) mfix) = map (unlit L) (cofix_subst mfix).
  Proof using Type.
    unfold cofix_subst. rewrite length_map. generalize #|mfix|.
    induction n; cbn; auto. now f_equal.
  Qed.

  Lemma unlit_cunfold_fix mfix idx :
    cunfold_fix (map (map_def (unlit L)) mfix) idx =
    option_map (fun p => (p.1, unlit L p.2)) (cunfold_fix mfix idx).
  Proof using Hcl.
    rewrite /cunfold_fix nth_error_map.
    destruct nth_error => //=. rewrite unlit_substl unlit_fix_subst //.
  Qed.

  Lemma unlit_cunfold_cofix mfix idx :
    cunfold_cofix (map (map_def (unlit L)) mfix) idx =
    option_map (fun p => (p.1, unlit L p.2)) (cunfold_cofix mfix idx).
  Proof using Hcl.
    rewrite /cunfold_cofix nth_error_map.
    destruct nth_error => //=. rewrite unlit_substl unlit_cofix_subst //.
  Qed.

  Lemma unlit_nil t : unlit [] t = t.
  Proof using Type.
    induction t using term_forall_list_ind; cbn;
      try solve [f_equal; eauto; solve_all].
    all: try solve [f_equal; eauto; solve_all; destruct x; unfold on_snd; cbn in *; f_equal; auto].
    all: try solve [f_equal; solve_all; destruct x; unfold map_def; cbn in *; f_equal; auto].
    all: try solve [f_equal; destruct p as [? []]; cbn in *; auto; depelim X; destruct p as [hd hv];
      rewrite /map_array_model; cbn; destruct a; cbn in *; f_equal; f_equal; eauto; solve_all].
  Qed.

End UnlitSyntax.

(** ** Numerals *)

Lemma numeral_ok_rect Σ (P : term -> Type) :
  (forall i c mdecl idecl cdecl, lookup_constructor Σ i c = Some (mdecl, idecl, cdecl) ->
     ind_npars mdecl = 0 -> cstr_nargs cdecl = 0 -> P (tConstruct i c [])) ->
  (forall i c mdecl idecl cdecl a, lookup_constructor Σ i c = Some (mdecl, idecl, cdecl) ->
     ind_npars mdecl = 0 -> cstr_nargs cdecl = 1 -> numeral_ok Σ a -> P a ->
     P (tApp (tConstruct i c []) a)) ->
  forall s, numeral_ok Σ s -> P s.
Proof.
  intros H0 H1. induction s; cbn; try discriminate.
  - destruct s1; try discriminate. destruct args; try discriminate.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl; try discriminate.
    move/andP => [/andP [hp hn] ha]. eapply H1; eauto. now apply/eqb_spec. now apply/eqb_spec.
  - destruct args; try discriminate.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl; try discriminate.
    move/andP => [hp hn]. eapply H0; eauto; now apply/eqb_spec.
Qed.

Section Numerals.
  Context (Σ : global_declarations).

  Lemma numeral_ok_mono Σ' s :
    (forall i c x, lookup_constructor Σ i c = Some x -> lookup_constructor Σ' i c = Some x) ->
    numeral_ok Σ s -> numeral_ok Σ' s.
  Proof.
    intros hm. revert s. apply numeral_ok_rect.
    - intros i c mdecl idecl cdecl hl hp hn. cbn. rewrite (hm _ _ _ hl) hp hn //.
    - intros i c mdecl idecl cdecl a hl hp hn _ ih. cbn. rewrite (hm _ _ _ hl) hp hn ih //.
  Qed.

  Lemma numeral_closed s k : numeral_ok Σ s -> closedn k s.
  Proof.
    revert s. apply numeral_ok_rect; cbn; intros; auto.
  Qed.

  Lemma numeral_unlit L s : numeral_ok Σ s -> unlit L s = s.
  Proof.
    revert s. apply numeral_ok_rect; cbn; intros; auto. now rewrite H3.
  Qed.

  Lemma numeral_mkApps s : numeral_ok Σ s -> exists i c args, s = mkApps (tConstruct i c []) args.
  Proof.
    revert s. apply numeral_ok_rect; intros.
    - now exists i, c, [].
    - now exists i, c, [a].
  Qed.

  Lemma numeral_wellformed {efl : EEnvFlags} k s :
    has_tApp -> has_tConstruct -> cstr_as_blocks = false -> numeral_ok Σ s -> wellformed Σ k s.
  Proof.
    intros ha hc hb. revert s. apply numeral_ok_rect; intros; cbn.
    - rewrite hc H hb //.
    - rewrite ha hc H hb H3 //.
  Qed.

  Lemma numeral_eval {wfl : WcbvFlags} s :
    with_constructor_as_block = false -> numeral_ok Σ s -> eval Σ s s.
  Proof.
    intros wcon. revert s. apply numeral_ok_rect; intros.
    - apply eval_atom. cbn [atom]. rewrite wcon H //.
    - eapply (eval_construct Σ i c mdecl idecl cdecl (tConstruct i c []) [] a a); auto.
      + apply eval_atom. cbn [atom mkApps]. rewrite wcon H //.
      + rewrite /cstr_arity H1; cbn; lia.
  Qed.

  Lemma numeral_isEtaExp Γ s : numeral_ok Σ s -> isEtaExp Σ Γ s.
  Proof.
    revert s. apply numeral_ok_rect; intros.
    - change (tConstruct i c []) with (mkApps (tConstruct i c []) []).
      rewrite isEtaExp_Constructor /isEtaExp_app /lookup_constructor_pars_args H /= H0 H1 //.
    - change (tApp (tConstruct i c []) a) with (mkApps (tConstruct i c []) [a]).
      rewrite isEtaExp_Constructor /isEtaExp_app /lookup_constructor_pars_args H /= H0 H1 H3 //.
  Qed.
End Numerals.

(** ** Relating the old and the new environment *)

Record lit_rel (L : lit_table) (Σ' Σ : global_declarations) : Prop := {
  lr_lit : forall kn s, lit_lookup L kn = Some s ->
    lookup_env Σ' kn = Some (ConstantDecl {| cst_body := Some s |}) /\ lookup_env Σ kn = None ;
  lr_other : forall kn, lit_lookup L kn = None ->
    option_map (unlit_decl L) (lookup_env Σ' kn) = lookup_env Σ kn }.

Section LitRel.
  Context {L : lit_table} {Σ' Σ : global_declarations} (R : lit_rel L Σ' Σ).

  Lemma lr_minductive kn : lookup_minductive Σ' kn = lookup_minductive Σ kn.
  Proof using R.
    unfold lookup_minductive. destruct (lit_lookup L kn) eqn:E.
    - now destruct (lr_lit _ _ _ R _ _ E) as [-> ->].
    - pose proof (lr_other _ _ _ R _ E) as h.
      destruct (lookup_env Σ' kn) as [[]|]; cbn in h; rewrite -h //.
  Qed.

  Lemma lr_lookup_inductive ind : lookup_inductive Σ' ind = lookup_inductive Σ ind.
  Proof using R. unfold lookup_inductive. now rewrite lr_minductive. Qed.

  Lemma lr_lookup_constructor ind c : lookup_constructor Σ' ind c = lookup_constructor Σ ind c.
  Proof using R. unfold lookup_constructor. now rewrite lr_lookup_inductive. Qed.

  Lemma lr_lookup_constructor_pars_args ind c :
    lookup_constructor_pars_args Σ' ind c = lookup_constructor_pars_args Σ ind c.
  Proof using R. unfold lookup_constructor_pars_args. now rewrite lr_lookup_constructor. Qed.

  Lemma lr_lookup_projection p : lookup_projection Σ' p = lookup_projection Σ p.
  Proof using R. unfold lookup_projection. now rewrite lr_lookup_constructor. Qed.

  Lemma lr_constructor_isprop_pars_decl ind c :
    constructor_isprop_pars_decl Σ' ind c = constructor_isprop_pars_decl Σ ind c.
  Proof using R. unfold constructor_isprop_pars_decl. now rewrite lr_lookup_constructor. Qed.

  Lemma lr_inductive_isprop_and_pars ind :
    inductive_isprop_and_pars Σ' ind = inductive_isprop_and_pars Σ ind.
  Proof using R. unfold inductive_isprop_and_pars. now rewrite lr_lookup_inductive. Qed.

  Lemma lr_constant kn cb : lit_lookup L kn = None -> lookup_env Σ kn = Some (ConstantDecl cb) ->
    exists cb', lookup_env Σ' kn = Some (ConstantDecl cb') /\
      option_map (unlit L) cb'.(cst_body) = cb.(cst_body).
  Proof using R.
    intros hn hl. pose proof (lr_other _ _ _ R _ hn) as h. rewrite hl in h.
    destruct (lookup_env Σ' kn) as [[cb'|]|]; cbn in h; try discriminate.
    injection h as h. subst cb. now exists cb'.
  Qed.

  Context (HS : forall kn s, lit_lookup L kn = Some s ->
                  exists i c args, s = mkApps (tConstruct i c []) args).

  Lemma unlit_isLambda t : isLambda (unlit L t) -> isLambda t.
  Proof using HS.
    destruct t; cbn; auto. destruct (lit_lookup L k) eqn:E; auto.
    destruct (HS _ _ E) as (i & c & args & ->).
    destruct args using rev_case; cbn; auto. rewrite mkApps_app //.
  Qed.

  Lemma wellformed_unlit {efl : EEnvFlags} :
    has_tConst -> forall k t, wellformed Σ k (unlit L t) -> wellformed Σ' k t.
  Proof using R HS.
    intros hc k t; induction t in k |- * using term_forall_list_ind; intros hw.
    all: cbn -[lookup_constructor lookup_inductive lookup_projection lookup_constructor_pars_args] in hw |- *.
    all: rewrite /wf_brs ?lr_lookup_constructor ?lr_lookup_inductive ?lr_lookup_projection
        ?lr_lookup_constructor_pars_args ?length_map.
    all: try rewrite /wf_brs length_map in hw.
    all: try solve [rtoProp; intuition auto; solve_all].
    - destruct (lit_lookup L s) eqn:E.
      + destruct (lr_lit _ _ _ R _ _ E) as [h _]. rewrite hc /lookup_constant h /= orb_true_r //.
      + rewrite hc. cbn in hw. move/andP: hw => [_ hw]. pose proof (lr_other _ _ _ R _ E) as h.
        move: hw. rewrite /lookup_constant -h. destruct (lookup_env Σ' s) as [[[b]|]|]; cbn; auto; destruct b; auto.
    - rewrite -/(wellformed Σ' k) in hw |- *.
      move: hw. rewrite ?length_map. destruct cstr_as_blocks; [|destruct args; cbn; auto]. rtoProp; intuition auto; solve_all.
    - move: hw; rewrite /wf_fix_gen length_map; rtoProp; intuition auto; solve_all.
      now apply unlit_isLambda.
    - move: hw; rewrite /wf_fix_gen length_map; rtoProp; intuition auto; solve_all.
    - move: hw; rewrite has_prim_map_prim; rtoProp; intuition auto.
      destruct p as [? []]; cbn in *; auto. depelim X. destruct p as [hd hv].
      move: H0; rewrite /test_array_model /map_array_model; cbn; rtoProp; intuition eauto; solve_all.
  Qed.
End LitRel.

(** ** The environments built by [hoist_program_table] *)

Lemma lookup_env_app Σ1 Σ2 kn :
  lookup_env (Σ1 ++ Σ2) kn = match lookup_env Σ1 kn with Some d => Some d | None => lookup_env Σ2 kn end.
Proof. induction Σ1 as [|[kn' d] Σ1 IH]; cbn; auto. destruct (eqb kn kn'); auto. Qed.

Lemma lit_lookup_cons kn' s L kn :
  lit_lookup ((kn', s) :: L) kn = if eqb kn kn' then Some s else lit_lookup L kn.
Proof.
  rewrite /lit_lookup /=. case: (eqb_spec kn kn') => [->|hne].
  - now rewrite eqb_refl.
  - case: (eqb_spec kn' kn) => [e|_]; [congruence|reflexivity].
Qed.

Lemma lookup_env_lits L kn :
  lookup_env (map lit_decl L) kn = option_map (fun s => ConstantDecl {| cst_body := Some s |}) (lit_lookup L kn).
Proof.
  induction L as [|[kn' s] L IH]; cbn; auto.
  rewrite lit_lookup_cons. destruct (eqb kn kn'); auto.
Qed.

Lemma lit_lookup_In L kn s : lit_lookup L kn = Some s -> In (kn, s) L.
Proof.
  induction L as [|[kn' s'] L IH]; cbn; [discriminate|].
  rewrite lit_lookup_cons. case: (eqb_spec kn kn') => [->|_].
  - intros [= ->]. now left.
  - intros h. right. now apply IH.
Qed.

Lemma eqb_true {A} {R : ReflectEq A} (x y : A) : x == y -> x = y.
Proof. now case: eqb_spec. Qed.

Definition decl_rel (L : lit_table) (d' d : kername × global_decl) : bool :=
  (d'.1 == d.1) && (unlit_decl L d'.2 == d.2).

Lemma forallb2_lookup L newer' newer kn :
  forallb2 (decl_rel L) newer' newer ->
  option_map (unlit_decl L) (lookup_env newer' kn) = lookup_env newer kn.
Proof.
  induction newer' as [|[kn' d'] newer' IH] in newer |- *; destruct newer as [|[kn0 d] newer]; cbn; auto;
    try discriminate.
  rewrite /decl_rel /=. move/andP => [/andP [h1 h2] h]. apply eqb_true in h1, h2. subst.
  destruct (eqb kn kn0); auto.
Qed.

Lemma forallb2_names L newer' newer :
  forallb2 (decl_rel L) newer' newer -> map fst newer' = map fst newer.
Proof.
  induction newer' as [|[kn' d'] newer' IH] in newer |- *; destruct newer as [|[kn0 d] newer]; cbn; auto;
    try discriminate.
  rewrite /decl_rel /=. move/andP => [/andP [h1 _] h]. apply eqb_true in h1. subst. f_equal. now apply IH.
Qed.

Lemma split_binnums_app Σ a b : split_binnums Σ = Some (a, b) -> Σ = a ++ b.
Proof.
  induction Σ as [|[kn d] Σ IH] in a, b |- *; cbn; [discriminate|].
  destruct is_binnums. { intros [= <- <-]. reflexivity. }
  destruct split_binnums as [[a' b']|]; cbn; [|discriminate].
  intros [= <- <-]. cbn. f_equal. now apply IH.
Qed.

Lemma unlit_wellformed_id {efl : EEnvFlags} L Σ0 k t :
  (forall kn s, lit_lookup L kn = Some s -> lookup_env Σ0 kn = None) ->
  wellformed Σ0 k t -> unlit L t = t.
Proof.
  intros hf. induction t in k |- * using term_forall_list_ind; intros hw.
  all: cbn -[lookup_constructor lookup_inductive lookup_projection lookup_constructor_pars_args] in hw |- *.
  all: rtoProp.
  all: try solve [f_equal; intuition eauto; solve_all;
    try (destruct x; unfold on_snd, map_def in *; cbn in *; f_equal; eauto)].
  - destruct (lit_lookup L s) eqn:E; auto. apply hf in E.
    rewrite /lookup_constant E in H0. discriminate.
  - f_equal. destruct cstr_as_blocks; rtoProp.
    + solve_all.
    + destruct args; cbn in *; auto; discriminate.
  - rewrite /wf_fix_gen in H0 H1; rtoProp; f_equal; solve_all;
    destruct x; unfold map_def in *; cbn in *; f_equal; eauto.
  - rewrite /wf_fix_gen in H0; rtoProp; f_equal; solve_all;
    destruct x; unfold map_def in *; cbn in *; f_equal; eauto.
Qed.


Lemma hoist_check_spec Σ newer older t newer' t' L :
  hoist_check Σ newer older t newer' t' L ->
  [/\ (forall p, In p L -> lookup_env Σ p.1 = None /\ numeral_ok older p.2),
      nodup_kernames (map fst L), unlit L t' = t & forallb2 (decl_rel L) newer' newer].
Proof.
  rewrite /hoist_check. move/andP => [/andP [/andP [h1 h2] h3] h4].
  split; auto.
  - intros p hin. eapply forallb_forall in h1; tea. move/andP: h1 => [/andP [h1 h1'] _].
    split; auto. destruct lookup_env; cbn in *; auto; discriminate.
  - now apply eqb_true.
Qed.

Lemma hoist_program_table_spec th p :
  hoist_program_table th p = (p, []) \/
  exists newer older newer' t' L, p.1 = newer ++ older /\
    hoist_program_table th p = ((newer' ++ map lit_decl L ++ older, t'), L) /\
    hoist_check p.1 newer older p.2 newer' t' L.
Proof.
  unfold hoist_program_table. destruct split_binnums as [[newer older]|] eqn:hs; [|now left].
  cbv zeta. destruct hoist_check eqn:hc; [right|now left].
  do 5 eexists; split; [now apply split_binnums_app|split; [reflexivity|exact hc]].
Qed.

Lemma fresh_global_iff kn Σ : fresh_global kn Σ <-> ~ In kn (map fst Σ).
Proof.
  unfold fresh_global. rewrite Forall_forall. split.
  - intros h hin. apply in_map_iff in hin as [x [<- hx]]. exact (h x hx eq_refl).
  - intros h x hx e. apply h. subst. now apply in_map.
Qed.

Lemma lookup_env_None_In Σ kn : lookup_env Σ kn = None -> ~ In kn (map fst Σ).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; auto.
  case: (eqb_spec kn kn') => [->|hne]; [discriminate|]. intros h [e|hin]; [congruence|]. now apply IH.
Qed.

Lemma map_fst_lits L : map fst (map lit_decl L) = map fst L.
Proof. rewrite map_map. now apply map_ext. Qed.

Lemma nodup_kernames_cons kn L : nodup_kernames (kn :: L) -> ~ In kn L /\ nodup_kernames L.
Proof.
  cbn. move/andP => [h1 h2]. split; auto. intros hin.
  move/negP: h1. apply. apply existsb_exists. exists kn. split; auto. apply eqb_refl.
Qed.

Lemma wf_glob_app {efl : EEnvFlags} Σ1 Σ2 : wf_glob (Σ1 ++ Σ2) -> wf_glob Σ2.
Proof. induction Σ1; cbn; auto. intros h; depelim h; auto. Qed.

Lemma extends_app {efl : EEnvFlags} Σ1 Σ2 : wf_glob (Σ1 ++ Σ2) -> extends Σ2 (Σ1 ++ Σ2).
Proof. intros wf. eapply EExtends.extends_prefix_extends; tea. now exists Σ1. Qed.

Lemma lookup_constructor_app {efl : EEnvFlags} Σ1 Σ2 i c x :
  wf_glob (Σ1 ++ Σ2) -> lookup_constructor Σ2 i c = Some x -> lookup_constructor (Σ1 ++ Σ2) i c = Some x.
Proof. intros wf. eapply extends_lookup_constructor; tea. now apply extends_app. Qed.

Lemma older_unlit_id {efl : EEnvFlags} L older :
  wf_glob older -> (forall kn s, lit_lookup L kn = Some s -> lookup_env older kn = None) ->
  forall kn d, lookup_env older kn = Some d -> unlit_decl L d = d.
Proof.
  intros wf hf kn d hl. pose proof (lookup_env_wellformed wf hl) as hw.
  destruct d as [[[b|]]|]; cbn in *; auto.
  now rewrite (unlit_wellformed_id L older 0 b hf hw).
Qed.

Lemma lit_rel_concrete L newer newer' older :
  forallb2 (decl_rel L) newer' newer ->
  (forall kn s, lit_lookup L kn = Some s -> lookup_env (newer ++ older) kn = None) ->
  (forall kn d, lookup_env older kn = Some d -> unlit_decl L d = d) ->
  lit_rel L (newer' ++ map lit_decl L ++ older) (newer ++ older).
Proof.
  intros hb hf hid. split.
  - intros kn s hs. split; [|now apply hf in hs].
    pose proof (hf _ _ hs) as hn. rewrite lookup_env_app in hn.
    pose proof (forallb2_lookup _ _ _ kn hb) as e.
    destruct (lookup_env newer kn); try discriminate.
    rewrite !lookup_env_app. destruct (lookup_env newer' kn); try discriminate.
    rewrite lookup_env_lits hs //.
  - intros kn hn. rewrite !lookup_env_app lookup_env_lits hn /=.
    pose proof (forallb2_lookup _ _ _ kn hb) as e.
    destruct (lookup_env newer' kn) eqn:E1; cbn in e |- *; rewrite -e //.
    destruct (lookup_env older kn) eqn:E2; cbn; auto. rewrite (hid _ _ E2) //.
Qed.

Lemma wf_glob_lits {efl : EEnvFlags} L older :
  has_tApp -> has_tConstruct -> cstr_as_blocks = false -> wf_glob older ->
  (forall p, In p L -> lookup_env older p.1 = None /\ numeral_ok older p.2) ->
  nodup_kernames (map fst L) -> wf_glob (map lit_decl L ++ older).
Proof.
  intros ha hc hb wf. induction L as [|[kn s] L IH]; cbn; auto.
  intros hL hnd. apply nodup_kernames_cons in hnd as [hnin hnd].
  have wf' : wf_glob (map lit_decl L ++ older) by apply IH; auto.
  destruct (hL (kn, s)) as [hn hs]; [now left|]. cbn in hn, hs.
  constructor; auto.
  - cbn. eapply numeral_wellformed; auto.
    eapply numeral_ok_mono; tea. intros. now apply lookup_constructor_app.
  - apply fresh_global_iff. rewrite map_app map_fst_lits. intros hin.
    apply in_app_or in hin as [hin|hin]; auto. now apply lookup_env_None_In in hn.
Qed.

Lemma wf_glob_newer {efl : EEnvFlags} L older newer newer' :
  has_tConst ->
  (forall kn s, lit_lookup L kn = Some s -> exists i c args, s = mkApps (tConstruct i c []) args) ->
  (forall kn d, lookup_env older kn = Some d -> unlit_decl L d = d) ->
  wf_glob (map lit_decl L ++ older) ->
  forallb2 (decl_rel L) newer' newer -> wf_glob (newer ++ older) ->
  (forall p, In p L -> lookup_env (newer ++ older) p.1 = None) ->
  wf_glob (newer' ++ map lit_decl L ++ older).
Proof.
  intros hc HS hid wfl.
  induction newer' as [|[kn' d'] newer' IH] in newer |- *; destruct newer as [|[kn d] newer]; cbn;
    try discriminate; auto.
  move/andP => [hd hb]. rewrite /decl_rel /= in hd. move/andP: hd => [h1 h2].
  apply eqb_true in h1, h2. subst.
  intros wf hf. depelim wf.
  have hf' : forall p, In p L -> lookup_env (newer ++ older) p.1 = None.
  { intros p hp. specialize (hf p hp). move: hf. case: eqb => //. }
  have hfl : forall kn s, lit_lookup L kn = Some s -> lookup_env (newer ++ older) kn = None.
  { intros kn0 s hs. now apply (hf' (kn0, s)), lit_lookup_In. }
  have R := lit_rel_concrete L newer newer' older hb hfl hid.
  constructor.
  - now apply (IH newer).
  - destruct d' as [[[b|]]|]; cbn in *; auto. eapply wellformed_unlit; tea.
  - apply fresh_global_iff. apply fresh_global_iff in H0.
    rewrite map_app (forallb2_names _ _ _ hb) map_app map_fst_lits.
    rewrite map_app in H0. intros hin. apply in_app_or in hin as [hin|hin].
    + apply H0. now apply in_or_app; left.
    + apply in_app_or in hin as [hin|hin].
      * apply in_map_iff in hin as [[kn0 s] [<- hin]]. specialize (hf _ hin). cbn in hf.
        now rewrite eqb_refl in hf.
      * apply H0. now apply in_or_app; right.
Qed.


Lemma hoist_facts {efl : EEnvFlags} L newer older newer' :
  wf_glob (newer ++ older) ->
  (forall p, In p L -> lookup_env (newer ++ older) p.1 = None /\ numeral_ok older p.2) ->
  forallb2 (decl_rel L) newer' newer ->
  [/\ lit_rel L (newer' ++ map lit_decl L ++ older) (newer ++ older),
      (forall kn s, lit_lookup L kn = Some s -> numeral_ok (newer ++ older) s),
      (forall kn s, lit_lookup L kn = Some s -> exists i c args, s = mkApps (tConstruct i c []) args),
      (forall p, In p L -> lookup_env older p.1 = None /\ numeral_ok older p.2) &
      wf_glob older].
Proof.
  intros wfg hL hdr.
  have wfo := wf_glob_app _ _ wfg.
  have hLo : forall p, In p L -> lookup_env older p.1 = None /\ numeral_ok older p.2.
  { intros p hp. destruct (hL p hp) as [h1 h2]. split; auto.
    rewrite lookup_env_app in h1. destruct (lookup_env newer p.1); [discriminate|auto]. }
  have hfo : forall kn s, lit_lookup L kn = Some s -> lookup_env older kn = None.
  { intros kn s hs. now apply lit_lookup_In, hLo in hs as [hs _]. }
  have hfl : forall kn s, lit_lookup L kn = Some s -> lookup_env (newer ++ older) kn = None.
  { intros kn s hs. now apply lit_lookup_In, hL in hs as [hs _]. }
  split; auto.
  - apply lit_rel_concrete; auto. now apply older_unlit_id.
  - intros kn s hs. apply lit_lookup_In, hLo in hs as [_ hs]. cbn in hs.
    eapply numeral_ok_mono; tea. intros. now apply lookup_constructor_app.
  - intros kn s hs. apply lit_lookup_In, hLo in hs as [_ hs]. now eapply numeral_mkApps.
Qed.


(** ** Eta-expansion *)

Lemma isEtaExp_mkApps_args Σ Γ f args : isEtaExp Σ Γ (mkApps f args) -> forallb (isEtaExp Σ Γ) args.
Proof.
  destruct (decompose_app f) as [hd a0] eqn:da.
  rewrite (decompose_app_inv da) -mkApps_app. pose proof (decompose_app_notApp _ _ _ da).
  rewrite isEtaExp_mkApps //. destruct expanded_head_viewc; rewrite ?forallb_app; rtoProp; intuition auto.
Qed.

Lemma rev_map_rarg_unlit L (mfix : mfixpoint term) :
  rev_map (fun x => S (rarg x)) (map (map_def (unlit L)) mfix) = rev_map (fun x => S (rarg x)) mfix.
Proof. rewrite !rev_map_spec map_map //. Qed.

Lemma isEtaExp_fixapp_unlit L mfix idx k :
  isEtaExp_fixapp (map (map_def (unlit L)) mfix) idx k = isEtaExp_fixapp mfix idx k.
Proof. rewrite /isEtaExp_fixapp nth_error_map. destruct nth_error => //. Qed.

Section EtaUnlit.
  Context {L : lit_table} {Σ' Σ : global_declarations} (R : lit_rel L Σ' Σ).
  Context (HS : forall kn s, lit_lookup L kn = Some s ->
                  exists i c args, s = mkApps (tConstruct i c []) args).

  Lemma isEtaExp_app_lr ind c k : isEtaExp_app Σ' ind c k = isEtaExp_app Σ ind c k.
  Proof using R. rewrite /isEtaExp_app (lr_lookup_constructor_pars_args R) //. Qed.

  Lemma isEtaExp_unlit Γ t : isEtaExp Σ Γ (unlit L t) -> isEtaExp Σ' Γ t.
  Proof using R HS.
    funelim (isEtaExp Σ' Γ t); simp isEtaExp; rewrite -?isEtaExp_equation_1.
    all: try (intros; reflexivity).
    all: try (match goal with |- is_true (isEtaExp _ _ (unlit _ (mkApps _ _))) -> _ => fail 1 | _ => idtac end;
      intros h; cbn [unlit map] in h; simp isEtaExp in h; rewrite -?isEtaExp_equation_1 in h;
      rewrite ?forallb_InP_spec ?test_primIn_spec in h).
    all: try solve [exact h | auto | rtoProp; auto | discriminate].
    all: try solve [rewrite isEtaExp_app_lr; rtoProp; split; auto; destruct block_args; cbn in *; auto].
    all: try solve [rtoProp; split; auto; eapply In_All in H0; solve_all].
    all: try solve [eapply In_All in H; solve_all].
    all: try solve [rewrite length_map in h; eapply In_All in H; solve_all].
    all: try solve [eapply InPrim_primProp in H; rewrite test_prim_map in h;
      destruct p as [? []]; cbn in *; auto; depelim H; destruct p as [hd hv];
      rewrite /test_array_model in h |- *; rtoProp; intuition auto; solve_all].
    - intros h. rewrite unlit_mkApps in h. cbn [unlit] in h. rewrite isEtaExp_mkApps // in h.
      cbn [expanded_head_viewc] in h. rewrite isEtaExp_app_lr. rewrite length_map in h.
      rtoProp; intuition auto. eapply In_All in H. solve_all. destruct block_args; cbn in *; auto.
    - intros h. rewrite unlit_mkApps in h. cbn [unlit] in h. rewrite isEtaExp_mkApps // in h.
      cbn [expanded_head_viewc] in h.
      rewrite rev_map_rarg_unlit isEtaExp_fixapp_unlit length_map in h.
      eapply In_All in H. eapply In_All in H0.
      rtoProp; intuition auto; solve_all; try (rtoProp; split; [now eapply (unlit_isLambda HS)|auto]).
    - intros h. rewrite unlit_mkApps in h. cbn [unlit] in h. rewrite isEtaExp_mkApps // in h.
      cbn [expanded_head_viewc] in h. rewrite length_map in h.
      rtoProp; intuition auto. eapply In_All in H. solve_all.
    - intros h. eapply In_All in H0.
      destruct u; try solve [simp discr_expanded_head in d; destruct d]; try discriminate.
      all: rewrite unlit_mkApps in h; cbn [unlit] in h.
      all: try (destruct (lit_lookup L k) as [s|] eqn:E;
        [apply isEtaExp_mkApps_args in h; simp isEtaExp; cbn; solve_all|]).
      all: rewrite isEtaExp_mkApps // in h; cbn [expanded_head_viewc] in h.
      all: rtoProp; split; [apply H; auto|solve_all].
      all: cbn [unlit]; rewrite E; auto.
  Qed.
End EtaUnlit.


Lemma lits_lookup_constructor L older i c :
  (forall p, In p L -> lookup_env older p.1 = None) ->
  lookup_constructor (map lit_decl L ++ older) i c = lookup_constructor older i c.
Proof.
  intros h. rewrite /lookup_constructor /lookup_inductive. f_equal. f_equal.
  unfold lookup_minductive. rewrite lookup_env_app lookup_env_lits.
  destruct (lit_lookup L (inductive_mind i)) eqn:E; cbn; auto.
  apply lit_lookup_In, h in E. cbn in E. rewrite E //.
Qed.

Lemma expanded_global_app Σ1 Σ2 : expanded_global_env (Σ1 ++ Σ2) -> expanded_global_env Σ2.
Proof. induction Σ1; cbn; auto. intros h; depelim h; auto. Qed.

Lemma expanded_global_lits L older :
  expanded_global_env older ->
  (forall p, In p L -> lookup_env older p.1 = None /\ numeral_ok older p.2) ->
  expanded_global_env (map lit_decl L ++ older).
Proof.
  intros eo. induction L as [|[kn s] L IH]; cbn; auto. intros hL.
  constructor.
  - apply IH. intros p hp. apply hL. now right.
  - cbn. apply isEtaExp_expanded. apply numeral_isEtaExp.
    destruct (hL (kn, s)) as [_ hs]; [now left|]. cbn in hs.
    eapply numeral_ok_mono; tea. intros i c x hx.
    rewrite lits_lookup_constructor //. intros p hp. apply hL. now right.
Qed.

Lemma expanded_global_newer {efl : EEnvFlags} L older newer newer' :
  (forall kn s, lit_lookup L kn = Some s -> exists i c args, s = mkApps (tConstruct i c []) args) ->
  (forall kn d, lookup_env older kn = Some d -> unlit_decl L d = d) ->
  expanded_global_env (map lit_decl L ++ older) ->
  forallb2 (decl_rel L) newer' newer -> expanded_global_env (newer ++ older) ->
  (forall p, In p L -> lookup_env (newer ++ older) p.1 = None) ->
  expanded_global_env (newer' ++ map lit_decl L ++ older).
Proof.
  intros HS hid el.
  induction newer' as [|[kn' d'] newer' IH] in newer |- *; destruct newer as [|[kn d] newer]; cbn;
    try discriminate; auto.
  move/andP => [hd hb]. rewrite /decl_rel /= in hd. move/andP: hd => [h1 h2].
  apply eqb_true in h1, h2. subst.
  intros eg hf. depelim eg.
  have hf' : forall p, In p L -> lookup_env (newer ++ older) p.1 = None.
  { intros p hp. specialize (hf p hp). move: hf. case: eqb => //. }
  have hfl : forall kn s, lit_lookup L kn = Some s -> lookup_env (newer ++ older) kn = None.
  { intros kn0 s hs. now apply (hf' (kn0, s)), lit_lookup_In. }
  have R := lit_rel_concrete L newer newer' older hb hfl hid.
  constructor.
  - now apply (IH newer).
  - destruct d' as [[[b|]]|]; cbn in *; auto.
    apply isEtaExp_expanded. eapply isEtaExp_unlit; tea. now apply expanded_isEtaExp.
Qed.


(** ** Evaluation *)

Section Sim.
  Context {wfl : WcbvFlags} (wcon : with_constructor_as_block = false).
  Context {L : lit_table} {Σ' Σ : global_declarations} (R : lit_rel L Σ' Σ).
  Context (HN : forall kn s, lit_lookup L kn = Some s -> numeral_ok Σ s).

  Lemma HN' kn s : lit_lookup L kn = Some s -> numeral_ok Σ' s.
  Proof using R HN.
    intros hs. eapply numeral_ok_mono; [|now eapply HN].
    intros. now rewrite (lr_lookup_constructor R).
  Qed.

  Lemma Hcl kn s : lit_lookup L kn = Some s -> closedn 0 s.
  Proof using HN. intros hs. eapply numeral_closed, HN; tea. Qed.

  Lemma HS kn s : lit_lookup L kn = Some s -> exists i c args, s = mkApps (tConstruct i c []) args.
  Proof using HN. intros hs. eapply numeral_mkApps, HN; tea. Qed.

  Lemma sim_lit kn s v : lit_lookup L kn = Some s -> eval Σ s v ->
    exists v', ∥ eval Σ' (tConst kn) v' ∥ /\ unlit L v' = v.
  Proof using wcon R HN.
    intros hs ev. have hn := HN _ _ hs.
    have e := eval_deterministic ev (numeral_eval Σ s wcon hn). subst v.
    exists s. split; [|now eapply numeral_unlit].
    destruct (lr_lit _ _ _ R _ _ hs) as [hl _]. sq.
    eapply (eval_delta Σ' kn {| cst_body := Some s |} s hl); [reflexivity|].
    apply numeral_eval; auto. now eapply HN'.
  Qed.

  Lemma value_head_not_const v : value Σ' v -> forall kn args, v = mkApps (tConst kn) args -> False.
  Proof.
    revert v. apply (value_values_ind (fun v => forall kn args, v = mkApps (tConst kn) args -> False)).
    - intros t ha kn args0 e. subst t. apply atom_mkApps in ha as [-> ha]. cbn in ha. discriminate.
    - intros p _ _ kn args0 e.
      destruct args0 using rev_case; cbn in e; [discriminate|rewrite mkApps_app in e; discriminate].
    - intros ind c mdecl idecl cdecl args _ _ _ _ _ kn args0 e.
      destruct args0 using rev_case; cbn in e; [discriminate|rewrite mkApps_app in e; discriminate].
    - intros f args vh _ _ _ kn args0 e.
      apply mkApps_eq_inj in e as [-> _]; auto. depelim vh. eapply value_head_nApp; tea.
  Qed.

  Lemma unlit_value_inv v h args : value Σ' v -> ~~ isApp h -> unlit L v = mkApps h args ->
    exists h' args', [/\ v = mkApps h' args', unlit L h' = h, map (unlit L) args' = args &
      forall kn, h' <> tConst kn].
  Proof.
    intros hv hh e. destruct (decompose_app v) as [h0 a0] eqn:da.
    rewrite (decompose_app_inv da) in hv e |- *. pose proof (decompose_app_notApp _ _ _ da) as hn0.
    assert (hc : forall kn, h0 <> tConst kn). { intros kn ->. eapply value_head_not_const; eauto. }
    rewrite unlit_mkApps in e. apply mkApps_eq_inj in e as [e1 e2]; auto.
    - exists h0, a0. split; auto.
    - destruct h0; cbn in *; auto. exfalso; eapply hc; reflexivity.
  Qed.

  Lemma inv_construct v ind c args : value Σ' v -> unlit L v = mkApps (tConstruct ind c []) args ->
    exists args', v = mkApps (tConstruct ind c []) args' /\ map (unlit L) args' = args.
  Proof.
    intros hv e. eapply unlit_value_inv in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct h'; cbn in e1; try discriminate; try (exfalso; eapply hc; reflexivity).
    injection e1 as e3 e4 e5. subst. destruct args0; [|discriminate]. now exists args'.
  Qed.

  Lemma inv_fix v mfix idx args : value Σ' v -> unlit L v = mkApps (tFix mfix idx) args ->
    exists mfix' args', [/\ v = mkApps (tFix mfix' idx) args', map (map_def (unlit L)) mfix' = mfix &
      map (unlit L) args' = args].
  Proof.
    intros hv e. eapply unlit_value_inv in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct h'; cbn in e1; try discriminate; try (exfalso; eapply hc; reflexivity).
    injection e1 as e3 e4. subst. now do 2 eexists.
  Qed.

  Lemma inv_cofix v mfix idx args : value Σ' v -> unlit L v = mkApps (tCoFix mfix idx) args ->
    exists mfix' args', [/\ v = mkApps (tCoFix mfix' idx) args', map (map_def (unlit L)) mfix' = mfix &
      map (unlit L) args' = args].
  Proof.
    intros hv e. eapply unlit_value_inv in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct h'; cbn in e1; try discriminate; try (exfalso; eapply hc; reflexivity).
    injection e1 as e3 e4. subst. now do 2 eexists.
  Qed.

  Lemma inv_lambda v na b : value Σ' v -> unlit L v = tLambda na b -> exists b', v = tLambda na b' /\ unlit L b' = b.
  Proof.
    intros hv e. eapply (unlit_value_inv _ _ []) in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct args'; [|discriminate]. destruct h'; cbn in e1; try discriminate; try (exfalso; eapply hc; reflexivity).
    injection e1 as e3 e4. subst. now eexists.
  Qed.

  Lemma inv_box v : value Σ' v -> unlit L v = tBox -> v = tBox.
  Proof.
    intros hv e. eapply (unlit_value_inv _ _ []) in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct args'; [|discriminate]. destruct h'; cbn in e1; try discriminate; auto.
    exfalso; eapply hc; reflexivity.
  Qed.

  Lemma inv_lazy v t : value Σ' v -> unlit L v = tLazy t -> exists t', v = tLazy t' /\ unlit L t' = t.
  Proof.
    intros hv e. eapply (unlit_value_inv _ _ []) in e as (h' & args' & [-> e1 e2 hc]); auto.
    destruct args'; [|discriminate]. destruct h'; cbn in e1; try discriminate; try (exfalso; eapply hc; reflexivity).
    injection e1 as e3. subst. now eexists.
  Qed.

  Lemma unlit_head_pred f :
    [/\ isFixApp f -> isFixApp (unlit L f), isConstructApp f -> isConstructApp (unlit L f),
        isPrimApp f -> isPrimApp (unlit L f) & isLazyApp f -> isLazyApp (unlit L f)].
  Proof.
    destruct (decompose_app f) as [h a] eqn:da. rewrite (decompose_app_inv da) unlit_mkApps
      !isFixApp_mkApps !isConstructApp_mkApps !isPrimApp_mkApps !isLazyApp_mkApps.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct h; cbn in *; try discriminate; split; auto.
  Qed.

  Lemma unlit_isFix f : isFix f -> isFix (unlit L f).
  Proof. destruct f; cbn; auto. Qed.
  Lemma unlit_isBox f : isBox f -> isBox (unlit L f).
  Proof. destruct f; cbn; auto. Qed.
  Lemma unlit_isLambda' f : isLambda f -> isLambda (unlit L f).
  Proof. destruct f; cbn; auto. Qed.

  Lemma sim_atom x' : atom Σ (unlit L x') -> eval Σ (unlit L x') (unlit L x') ->
    exists v', ∥ eval Σ' x' v' ∥ /\ unlit L v' = unlit L x'.
  Proof using wcon R HN.
    intros ha ev.
    enough (h : (exists k s, x' = tConst k /\ lit_lookup L k = Some s) \/ atom Σ' x').
    { destruct h as [(k & s & -> & E)|h].
      - cbn in ev |- *. rewrite E in ev |- *. eapply sim_lit; tea.
      - exists x'. split; [sq; now apply eval_atom|reflexivity]. }
    destruct x'; cbn in ha |- *; try discriminate; try (right; reflexivity).
    - destruct (lit_lookup L k) eqn:E; [left; eauto| cbn in ha; discriminate].
    - right. destruct args; cbn in ha |- *; [rewrite (lr_lookup_constructor R)|discriminate]; auto.
  Qed.

  Lemma app_cong_pred f :
    ~~ (isLambda (unlit L f) || (if with_guarded_fix then isFixApp (unlit L f) else isFix (unlit L f))
        || isBox (unlit L f) || isConstructApp (unlit L f) || isPrimApp (unlit L f) || isLazyApp (unlit L f)) ->
    ~~ (isLambda f || (if with_guarded_fix then isFixApp f else isFix f)
        || isBox f || isConstructApp f || isPrimApp f || isLazyApp f).
  Proof.
    apply contraNN. destruct (unlit_head_pred f) as [h1 h2 h3 h4].
    move/orP => [/orP [/orP [/orP [/orP [h|h]|h]|h]|h]|h].
    - rewrite (unlit_isLambda' _ h) //.
    - destruct with_guarded_fix.
      + rewrite (h1 h) orb_true_r //.
      + rewrite (unlit_isFix _ h) orb_true_r //.
    - rewrite (unlit_isBox _ h) orb_true_r //.
    - rewrite (h2 h) orb_true_r //.
    - rewrite (h3 h) orb_true_r //.
    - rewrite (h4 h) orb_true_r //.
  Qed.

  Ltac lit_tac := match goal with
    | [ Hx : match lit_lookup ?L ?k with Some _ => _ | None => tConst ?k end = _ |- _ ] =>
      let E := fresh "E" in let s := fresh "s" in
      destruct (lit_lookup L k) as [s|] eqn:E; [subst s; eapply sim_lit; tea | try discriminate]
    end.

  Lemma sim_list l l' :
    All2 (fun t v => eval Σ t v -> forall t', unlit L t' = t ->
      exists v', ∥ eval Σ' t' v' ∥ /\ unlit L v' = v) (map (unlit L) l) l' ->
    All2 (eval Σ) (map (unlit L) l) l' ->
    exists vs, ∥ All2_Set (eval Σ') l vs ∥ /\ map (unlit L) vs = l'.
  Proof.
    induction l in l' |- *; intros h1 h2; cbn in h1, h2; depelim h1; depelim h2.
    - exists []. split; [sq; constructor|reflexivity].
    - destruct (e e0 a eq_refl) as [v1 [[ev1] e1]].
      destruct (IHl _ h1 h2) as [vs [[hvs] evs]].
      exists (v1 :: vs). split; [sq; now constructor|cbn; congruence].
  Qed.

  Lemma sim t v : eval Σ t v -> forall t', unlit L t' = t -> exists v', ∥ eval Σ' t' v' ∥ /\ unlit L v' = v.
  Proof using wcon R HN.
    intros ev. pose proof ev as ev0. revert ev0. induction ev; intros ev0 x' Hx.
    all: try congruence.
    all: try solve [subst; eapply sim_atom; tea].
    all: destruct x'; cbn [unlit] in Hx; try discriminate; try lit_tac.
    all: try (injection Hx; clear Hx; intros; subst).
    - (* box *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply inv_box in e1'; [|now eapply eval_to_value]. subst v1.
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']].
      exists tBox. split; [sq; eapply eval_box; tea|reflexivity].
    - (* beta *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply inv_lambda in e1' as [b' [-> eb]]; [|now eapply eval_to_value].
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']].
      destruct (IHev3 ev3 (csubst v2 0 b')) as [v3 [[ev3'] e3']].
      { rewrite (unlit_csubst L Hcl) e2' eb //. }
      exists v3. split; [sq; eapply eval_beta; tea|auto].
    - (* zeta *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      destruct (IHev2 ev2 (csubst v1 0 x'2)) as [v2 [[ev2'] e2']].
      { rewrite (unlit_csubst L Hcl) e1' //. }
      exists v2; split; [sq; eapply eval_zeta; tea|auto].
    - (* iota *)
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_construct in e1' as [args' [-> ea]]; [|now eapply eval_to_value]. subst args.
      rewrite nth_error_map in e2. destruct (nth_error brs0 c) as [br'|] eqn:Eb; cbn in e2; [|discriminate].
      injection e2 as e2. subst br.
      destruct (IHev2 ev2 (iota_red pars args' br')) as [v2 [[ev2'] e2']].
      { rewrite (unlit_iota_red L Hcl) //. }
      exists v2; split; [|auto]. sq.
      eapply (eval_iota Σ' ind pars cdecl x' c args' brs0 br' v2 wcon ev1'); tea.
      + rewrite (lr_constructor_isprop_pars_decl R) //.
      + now rewrite length_map in e3.
      + move: e4. rewrite !length_skipn length_map //.
    - (* iota_sing *)
      destruct brs0 as [|[n' f'] [|]]; cbn in H; try discriminate. injection H as e5 e6. subst n f4.
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_box in e1'; [|now eapply eval_to_value]. subst v1.
      destruct (IHev2 ev2 (substl (repeat tBox #|n'|) f')) as [v2 [[ev2'] e2']].
      { rewrite (unlit_substl L Hcl) map_repeat //. }
      exists v2; split; [|auto]. sq. eapply eval_iota_sing; tea.
      + rewrite (lr_inductive_isprop_and_pars R) //.
      + reflexivity.
    - (* fix *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply inv_fix in e1' as (mfix' & argsv' & [-> em ea]); [|now eapply eval_to_value]. subst mfix argsv.
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']]. subst av.
      rewrite (unlit_cunfold_fix L Hcl) in e1.
      destruct (cunfold_fix mfix' idx) as [[n' fn']|] eqn:Ec; cbn in e1; [|discriminate].
      injection e1 as e5 e6. subst fn. rewrite length_map in e5. subst n'.
      destruct (IHev3 ev3 (tApp (mkApps fn' argsv') v2)) as [v3 [[ev3'] e3']].
      { cbn [unlit]. rewrite unlit_mkApps //. }
      exists v3; split; [|auto]. sq. eapply eval_fix; tea.
    - (* fix_value *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply inv_fix in e1' as (mfix' & argsv' & [-> em ea]); [|now eapply eval_to_value]. subst mfix argsv.
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']]. subst av.
      rewrite (unlit_cunfold_fix L Hcl) in e1.
      destruct (cunfold_fix mfix' idx) as [[n' fn']|] eqn:Ec; cbn in e1; [|discriminate].
      injection e1 as e5 e6. subst.
      exists (tApp (mkApps (tFix mfix' idx) argsv') v2). split.
      + sq. eapply eval_fix_value; tea. now rewrite length_map in l.
      + cbn [unlit]. rewrite unlit_mkApps //.
    - (* fix' *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply (inv_fix _ _ _ []) in e1' as (mfix' & args'' & [-> em ea]); [|now eapply eval_to_value].
      destruct args''; [|discriminate]. subst mfix. cbn [mkApps] in ev1'.
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']]. subst av.
      rewrite (unlit_cunfold_fix L Hcl) in e0.
      destruct (cunfold_fix mfix' idx) as [[n' fn']|] eqn:Ec; cbn in e0; [|discriminate].
      injection e0 as e5 e6. subst.
      destruct (IHev3 ev3 (tApp fn' v2)) as [v3 [[ev3'] e3']]; [reflexivity|].
      exists v3; split; [|auto]. sq. eapply eval_fix'; tea.
    - (* cofix_case *)
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_cofix in e1' as (mfix' & args' & [-> em ea]); [|now eapply eval_to_value]. subst mfix args.
      rewrite (unlit_cunfold_cofix L Hcl) in e0.
      destruct (cunfold_cofix mfix' idx) as [[n' fn']|] eqn:Ec; cbn in e0; [|discriminate].
      injection e0 as e5 e6. subst.
      destruct (IHev2 ev2 (tCase ip (mkApps fn' args') brs0)) as [v2 [[ev2'] e2']].
      { cbn [unlit]. rewrite unlit_mkApps //. }
      exists v2; split; [|auto]. sq. eapply eval_cofix_case; tea.
    - (* cofix_proj *)
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_cofix in e1' as (mfix' & args' & [-> em ea]); [|now eapply eval_to_value]. subst mfix args.
      rewrite (unlit_cunfold_cofix L Hcl) in e0.
      destruct (cunfold_cofix mfix' idx) as [[n' fn']|] eqn:Ec; cbn in e0; [|discriminate].
      injection e0 as e5 e6. subst.
      destruct (IHev2 ev2 (tProj p (mkApps fn' args'))) as [v2 [[ev2'] e2']].
      { cbn [unlit]. rewrite unlit_mkApps //. }
      exists v2; split; [|auto]. sq. eapply eval_cofix_proj; tea.
    - (* delta *)
      destruct (lr_constant R c decl E isdecl) as [cb' [hl hb]]. rewrite e in hb.
      destruct (cst_body cb') as [b'|] eqn:Eb; cbn in hb; [|discriminate]. injection hb as hb.
      destruct (IHev ev b' hb) as [v1 [[ev1'] e1']].
      exists v1. split; [|auto]. sq. eapply eval_delta; tea.
    - (* proj *)
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_construct in e1' as [args' [-> ea]]; [|now eapply eval_to_value]. subst args.
      rewrite nth_error_map in e3. destruct (nth_error args' _) as [a'|] eqn:Ea; cbn in e3; [|discriminate].
      injection e3 as e3. subst a.
      destruct (IHev2 ev2 a' eq_refl) as [v2 [[ev2'] e2']].
      exists v2; split; [|auto]. sq. eapply eval_proj; tea.
      + rewrite (lr_constructor_isprop_pars_decl R); exact e1.
      + now rewrite length_map in e2.
    - (* proj_prop *)
      destruct (IHev ev x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_box in e1'; [|now eapply eval_to_value]. subst v1.
      exists tBox; split; [|reflexivity]. sq. eapply eval_proj_prop; tea.
      rewrite (lr_inductive_isprop_and_pars R) //.
    - (* construct *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      apply inv_construct in e1' as [args' [-> ea]]; [|now eapply eval_to_value]. subst args.
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']].
      exists (tApp (mkApps (tConstruct ind c []) args') v2). split.
      + sq. eapply eval_construct; tea.
        * rewrite (lr_lookup_constructor R); exact e0.
        * now rewrite length_map in l.
      + cbn [unlit]. rewrite unlit_mkApps. cbn. congruence.
    - (* app_cong *)
      destruct (IHev1 ev1 x'1 eq_refl) as [v1 [[ev1'] e1']].
      destruct (IHev2 ev2 x'2 eq_refl) as [v2 [[ev2'] e2']].
      exists (tApp v1 v2). split; [|cbn; congruence].
      sq. eapply eval_app_cong; tea. apply app_cong_pred. now rewrite e1'.
    - (* prim *)
      destruct prim as [tag m]; destruct m; cbn in X; depelim X.
      1-3: eexists; split; [sq; constructor; constructor|reflexivity].
      pose proof (fst (All2_over_undep ev1 (fun t v => eval Σ t v -> forall t', unlit L t' = t ->
        exists v', ∥ eval Σ' t' v' ∥ /\ unlit L v' = v)) a0) as h1.
      destruct (sim_list _ _ h1 (All2_Set_All2 _ _ _ ev1)) as [vs [[hvs] evs]].
      destruct (e ed (array_default a) eq_refl) as [d' [[hd] ed']].
      destruct a as [ad av]; cbn in *.
      exists (tPrim (prim_array {| array_default := d'; array_value := vs |})). split.
      + sq. constructor. exact (evalPrimArray (eval Σ') av ad vs d' hvs hd).
      + cbn. rewrite /map_array_model /=. subst a'. now rewrite evs ed'.
    - (* force *)
      destruct (IHev1 ev1 x' eq_refl) as [v1 [[ev1'] e1']].
      apply inv_lazy in e1' as [t'' [-> et]]; [|now eapply eval_to_value].
      destruct (IHev2 ev2 t'' et) as [v2 [[ev2'] e2']].
      exists v2; split; [|auto]. sq. eapply eval_force; tea.
  Qed.
End Sim.

(** ** Correctness *)

Section Correctness.
  Context {fl : WcbvFlags} {efl : EEnvFlags}.

  Lemma hoist_program_wf (th : nat) (p : eprogram) :
    has_tApp -> has_tConst -> has_tConstruct -> cstr_as_blocks = false ->
    wf_eprogram efl p -> wf_eprogram efl (hoist_program th p).
  Proof.
    intros ha hc hcs hb [wfg wft].
    unfold hoist_program.
    destruct (hoist_program_table_spec th p) as [e|(newer & older & newer' & t' & L & hsplit & e & hck)];
      rewrite e; [split; auto|]. cbn.
    apply hoist_check_spec in hck as [hL hnd ht hdr].
    destruct p as [Σ t]; cbn in *. subst Σ.
    destruct (hoist_facts L newer older newer' wfg hL hdr) as [R HN HS hLo wfo].
    have hfo : forall kn s, lit_lookup L kn = Some s -> lookup_env older kn = None.
    { intros kn s hs. now apply lit_lookup_In, hLo in hs as [hs _]. }
    have wfl : wf_glob (map lit_decl L ++ older) by apply wf_glob_lits.
    split.
    - eapply wf_glob_newer; tea. now apply older_unlit_id. intros; now apply hL.
    - eapply wellformed_unlit; tea. now rewrite ht.
  Qed.

  Lemma hoist_program_expanded (th : nat) (p : eprogram) :
    wf_eprogram efl p ->
    expanded_eprogram p -> expanded_eprogram (hoist_program th p).
  Proof.
    intros [wfg wft] [eg et].
    unfold hoist_program.
    destruct (hoist_program_table_spec th p) as [e|(newer & older & newer' & t' & L & hsplit & e & hck)];
      rewrite e; [split; auto|]. cbn.
    apply hoist_check_spec in hck as [hL hnd ht hdr].
    destruct p as [Σ t]; cbn in *. subst Σ.
    destruct (hoist_facts L newer older newer' wfg hL hdr) as [R HN HS hLo wfo].
    have hfo : forall kn s, lit_lookup L kn = Some s -> lookup_env older kn = None.
    { intros kn s hs. now apply lit_lookup_In, hLo in hs as [hs _]. }
    split.
    - eapply expanded_global_newer; tea.
      + now apply older_unlit_id.
      + apply expanded_global_lits; auto. now eapply expanded_global_app.
      + intros; now apply hL.
    - apply isEtaExp_expanded. eapply isEtaExp_unlit; tea. rewrite ht. now apply expanded_isEtaExp.
  Qed.

  Lemma hoist_program_lookup_inductive (th : nat) (p : eprogram) ind :
    lookup_inductive (hoist_program th p).1 ind = lookup_inductive p.1 ind.
  Proof.
    unfold hoist_program.
    destruct (hoist_program_table_spec th p) as [e|(newer & older & newer' & t' & L & hsplit & e & hck)];
      rewrite e; [reflexivity|]. cbn.
    apply hoist_check_spec in hck as [hL hnd ht hdr].
    rewrite hsplit in hL |- *.
    unfold lookup_inductive. f_equal.
    unfold lookup_minductive. rewrite !lookup_env_app lookup_env_lits.
    pose proof (forallb2_lookup _ _ _ (inductive_mind ind) hdr) as e'.
    destruct (lookup_env newer' (inductive_mind ind)) as [g|] eqn:E1; cbn in e' |- *; rewrite -e'.
    - destruct g; reflexivity.
    - destruct (lit_lookup L (inductive_mind ind)) as [s|] eqn:E; cbn; auto.
      apply lit_lookup_In, hL in E as [E _]. cbn in E.
      rewrite lookup_env_app -e' in E. now rewrite E.
  Qed.

  (** Evaluation is preserved up to unfolding the hoisted constants in the
      value. *)
  Lemma hoist_program_eval (th : nat) (p : eprogram) v :
    with_constructor_as_block = false ->
    wf_eprogram efl p ->
    eval p.1 p.2 v ->
    ∃ v', ∥ eval (hoist_program th p).1 (hoist_program th p).2 v' ∥
          ∧ unlit (hoist_program_table th p).2 v' = v.
  Proof.
    intros wcon [wfg wft] ev.
    unfold hoist_program.
    destruct (hoist_program_table_spec th p) as [e|(newer & older & newer' & t' & L & hsplit & e & hck)];
      rewrite e; cbn.
    - exists v. split; [now sq|]. apply unlit_nil.
    - apply hoist_check_spec in hck as [hL hnd ht hdr].
      destruct p as [Σ t]; cbn in *. subst Σ.
      destruct (hoist_facts L newer older newer' wfg hL hdr) as [R HN HS hLo wfo].
      exact (sim wcon R HN _ _ ev t' ht).
  Qed.

End Correctness.

Local Obligation Tactic := idtac.

Program Definition hoist_numerals_transformation {fl : WcbvFlags} {efl : EEnvFlags} (th : nat)
  (wcon : with_constructor_as_block = false)
  (hasapp : has_tApp) (hasconst : has_tConst) (hascstr : has_tConstruct)
  (noblocks : cstr_as_blocks = false) :
  Transform.t _ _ _ _ _ _ (eval_eprogram_mapping fl) (eval_eprogram_mapping fl) :=
  {| name := "hoisting numerals"%bs;
     pre p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 ∧ wf_eprogram efl p.2
              ∧ preserves_expansion true p.2;
     transform p _ := (p.1, hoist_program th p.2);
     post p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 ∧ wf_eprogram efl p.2
              ∧ preserves_expansion true p.2;
     obseq p _ p' v v' := unlit (hoist_program_table th p.2).2 v' = v |}.
Next Obligation.
  intros fl efl th wcon hasapp hasconst hascstr noblocks [m p] [hm [hwf hexp]]; cbn in *.
  split; [|split].
  - move: hm. rewrite /EReorderCstrs.wf_inductives_mapping.
    erewrite forallb_ext; [exact|].
    intros [ind [na tags]]. rewrite /EReorderCstrs.wf_inductive_mapping.
    now rewrite hoist_program_lookup_inductive.
  - now apply hoist_program_wf.
  - now apply hoist_program_expanded.
Qed.
Next Obligation.
  intros fl efl th wcon hasapp hasconst hascstr noblocks [m p] v [hm [hwf hexp]] [ev]; cbn in *.
  destruct (hoist_program_eval (fl := fl) (efl := efl) th p v wcon hwf ev) as [v' [ev' hv']].
  exists v'. split => //.
Qed.
