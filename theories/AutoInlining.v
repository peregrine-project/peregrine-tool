(** * Automatic inlining of constants

    Peregrine inlines exactly the constants listed in [inlinings_opts] (from
    the configuration or from [--attributes] files) with MetaRocq's
    [EInlining.inline_transformation].  That pass is correct for an
    arbitrary set of constants ([EInlining.inlining_wf],
    [EInlining.inlining_pres]: the only premises are that the program is
    wellformed and conditions on the flags): it goes through the environment
    from the oldest declaration to the newest, replaces in each body the
    occurrences (applied or not) of the constants of the set that are
    declared earlier and have a body by their already inlined body, and keeps
    all declarations.  A constant is therefore never inlined into itself,
    and the pass terminates for every set.  The functions of this file only
    compute sets; nothing here has to be trusted.

    Two sets, both computed from the program before the transformations, as
    [RecursorInlining.recursor_inlinings] is:

    - [standard_inlinings]: the constants Rocq's extraction always inlines
      ([manual_inline_set] in plugins/extraction/mlutil.ml) which the program
      declares with a body.

    - [small_inlinings limit]: the small constants, after [inline_test] of
      Rocq's extraction (its [AutoInline] option).  A constant is chosen if
      + it has a body which contains no fixpoint or cofixpoint (so it is not
        recursive, and no fixpoint is duplicated),
      + the body is a value: a lambda, a box, a constant, or a constructor
        applied to values (inlining never duplicates or delays a computation
        which the constant would do once),
      + its size is less than [limit].  The size is [Mlutil.ml_size]-like
        (see [inl_size]; the same measure as [ELboxOpts.ml_size]): constants
        count 0, as in Rocq,
      + the size of its inlined body, where a constant which has itself been
        chosen counts for the size of its own inlined body, is less than
        [inline_growth_factor * limit].  This is the size of what an
        occurrence receives, so chains of small constants cannot blow up:
        whatever is inlined at one occurrence is smaller than that bound.
      Unlike Rocq, strictness is not looked at ([is_not_strict]): evaluation
      is call by value, and replacing a constant by a body which is a value
      does not change what is evaluated, whether the occurrence is applied or
      not.

    Neither set contains
    - a constant the configuration remaps (the backend realises it),
    - a constant excluded by name ([inline_excluded], [--no-inline NAME];
      [NAME] is the full name of the constant as [string_of_kername] prints
      it, e.g. [Corelib.Init.Datatypes.andb]),
    - the constant which is the program's main term (backends name the entry
      point after it). *)

From Stdlib Require Import List Bool.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require BasicAst.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure Require EAstUtils.
From MetaRocq.Erasure.Typed Require ExAst.
From Peregrine Require Import Config PAst.

Import ListNotations.
Local Open Scope bs_scope.

Record inline_opts := {
  inline_standard   : bool;        (* --inline-standard-constants *)
  inline_small      : bool;        (* --inline-small-constants *)
  inline_size_limit : nat;         (* --inline-size-limit N *)
  inline_excluded   : list string; (* --no-inline NAME *)
}.

Definition default_inline_size_limit : nat := 12.

(** Bound on the size of an inlined body, in multiples of the limit. *)
Definition inline_growth_factor : nat := 2.

Definition no_inline_opts : inline_opts := {|
  inline_standard   := false;
  inline_small      := false;
  inline_size_limit := default_inline_size_limit;
  inline_excluded   := [];
|}.

(** ** The standard set *)

Definition standard_inline_names : list kername :=
  let wf := MPfile ["Wf"; "Init"; "Corelib"] in
  let datatypes := MPfile ["Datatypes"; "Init"; "Corelib"] in
  let logic := MPfile ["Logic"; "Init"; "Corelib"] in
  let specif := MPfile ["Specif"; "Init"; "Corelib"] in
  [ (wf, "well_founded_induction_type"); (wf, "well_founded_induction");
    (wf, "Acc_iter"); (wf, "Fix_F"); (wf, "Fix");
    (datatypes, "andb"); (datatypes, "orb");
    (logic, "eq_rec_r"); (logic, "eq_rect_r");
    (specif, "proj1_sig") ].

(** ** The size of a body *)

Section Size.
  (** The size of the inlined body of the constants chosen so far. *)
  Context (csize : kername -> nat).

  (** Applied arguments which are not boxes, lambdas, cases, lets and
      projections count 1; variables, boxes, primitive values and
      constructor heads 0; a constant counts [csize]. *)
  Fixpoint inl_size (t : term) : nat :=
    match t with
    | tApp f a => match a with tBox => inl_size f | _ => 1 + inl_size f + inl_size a end
    | tLambda _ b => 1 + inl_size b
    | tLetIn _ v b => 1 + inl_size v + inl_size b
    | tConstruct _ _ args => list_sum (map inl_size args)
    | tCase _ d brs => 1 + inl_size d + list_sum (map (fun br => inl_size (snd br)) brs)
    | tProj _ c => 1 + inl_size c
    | tFix mfix _ | tCoFix mfix _ => list_sum (map (fun d => inl_size (dbody d)) mfix)
    | tEvar _ args => list_sum (map inl_size args)
    | tLazy t | tForce t => inl_size t
    | tConst kn => csize kn
    | tRel _ | tVar _ | tBox | tPrim _ => 0
    end.
End Size.

Fixpoint has_fix (t : term) : bool :=
  match t with
  | tFix _ _ | tCoFix _ _ => true
  | tApp f a => has_fix f || has_fix a
  | tLambda _ b => has_fix b
  | tLetIn _ v b => has_fix v || has_fix b
  | tConstruct _ _ args => existsb has_fix args
  | tCase _ d brs => has_fix d || existsb (fun br => has_fix (snd br)) brs
  | tProj _ c => has_fix c
  | tEvar _ args => existsb has_fix args
  | tLazy t | tForce t => has_fix t
  | tPrim _ => true (* arrays may contain terms: not looked into *)
  | tRel _ | tVar _ | tBox | tConst _ => false
  end.

(** Lambdas, boxes, constants and constructors applied to such values. *)
Fixpoint inl_value (t : term) : bool :=
  match t with
  | tLambda _ _ | tBox | tConst _ => true
  | tConstruct _ _ args => forallb inl_value args
  | tApp f a =>
      inl_value f && inl_value a &&
      match EAstUtils.head f with tConstruct _ _ _ => true | _ => false end
  | _ => false
  end.

(** ** The sets *)

Section Generic.
  (** [decl] is [EAst.global_decl] or [ExAst.global_decl]. *)
  Context {decl : Type} (body : decl -> option term).
  Context (skip : kername -> bool).

  Definition standard_inlinings_env (env : list (kername * decl)) : list kername :=
    List.filter (fun kn =>
      negb (skip kn) &&
      List.existsb (fun '(kn', d) =>
        eq_kername kn kn' && match body d with Some _ => true | None => false end) env)
      standard_inline_names.

  Definition small_step (limit : nat) (st : KernameMap.t nat * list kername)
    (d : kername * decl) : KernameMap.t nat * list kername :=
    let '(sizes, acc) := st in
    let '(kn, d) := d in
    match body d with
    | Some b =>
        if skip kn || has_fix b || negb (inl_value b) then st
        else
          let s := inl_size (fun kn => match KernameMap.find kn sizes with
                                       | Some n => n | None => 0 end) b in
          if Nat.ltb (inl_size (fun _ => 0) b) limit && Nat.ltb s (inline_growth_factor * limit)
          then (KernameMap.add kn s sizes, kn :: acc) else st
    | None => st
    end.

  (** The environment has its newest declaration first; the constants are
      visited from the oldest, as the inlining pass does. *)
  Definition small_inlinings_env (limit : nat) (env : list (kername * decl)) : list kername :=
    List.rev (snd (List.fold_left (small_step limit) (List.rev env) (KernameMap.empty nat, []))).
End Generic.

Definition east_body (d : EAst.global_decl) : option term :=
  match d with EAst.ConstantDecl cb => cb.(EAst.cst_body) | _ => None end.

Definition exast_body (d : ExAst.global_decl) : option term :=
  match d with ExAst.ConstantDecl cb => cb.(ExAst.cst_body) | _ => None end.

Definition main_const (p : PAst) : option kername :=
  match p with
  | Untyped _ (Some (tConst kn)) | Typed _ (Some (tConst kn)) => Some kn
  | _ => None
  end.

Definition auto_inlinings (o : inline_opts) (remapped : kername -> bool) (p : PAst) : list kername :=
  let skip kn :=
    remapped kn ||
    List.existsb (String.eqb (string_of_kername kn)) o.(inline_excluded) ||
    match main_const p with Some kn' => eq_kername kn kn' | None => false end in
  let on_env {decl} (body : decl -> option term) (env : list (kername * decl)) :=
    List.app
      (if o.(inline_standard) then standard_inlinings_env body skip env else [])
      (if o.(inline_small) then small_inlinings_env body skip o.(inline_size_limit) env else []) in
  match p with
  | Untyped env _ => on_env east_body env
  | Typed env _ => on_env exast_body (List.map (fun '(kn, _, d) => (kn, d)) env)
  end.

(** The same list, as the attribute file the options stand for. *)
Definition auto_inline_attributes (o : inline_opts) (remapped : kername -> bool) (p : PAst)
  : attributes_config := {|
  inlinings_opt         := auto_inlinings o remapped p;
  const_remappings_opt  := [];
  ind_remappings_opt    := [];
  cstr_reorders_opt     := [];
  custom_attributes_opt := [];
|}.

(** ** Checks *)

Module AutoInliningChecks.

  Definition mp : modpath := MPfile ["M"].
  Definition dt : modpath := MPfile ["Datatypes"; "Init"; "Corelib"].
  Definition cst (b : term) : EAst.global_decl := EAst.ConstantDecl {| EAst.cst_body := Some b |}.
  Definition ax : EAst.global_decl := EAst.ConstantDecl {| EAst.cst_body := None |}.
  Definition lam := tLambda BasicAst.nAnon.
  Definition I : inductive := {| inductive_mind := (mp, "I"); inductive_ind := 0 |}.
  Definition fx : term :=
    tFix [ {| dname := BasicAst.nAnon; dbody := lam (tRel 0); rarg := 0 |} ] 0.

  (* newest first *)
  Definition env : untyped_env :=
    [ ((mp, "main"), cst (lam (tRel 0)));
      (* size 3; inlined size 1 + (1 + 5 + (1 + 5 + 0)) = 13 < 2 * 12 *)
      ((mp, "four"), cst (lam (tApp (tConst (mp, "twice")) (tApp (tConst (mp, "twice")) (tRel 0)))));
      ((mp, "twice"), cst (lam (lam (tApp (tApp (tRel 1) (tRel 0)) (tApp (tRel 1) (tRel 0))))));
      ((mp, "caf"), cst (tApp (tConst (mp, "id")) (tConstruct I 0 [])));
      ((mp, "one"), cst (tApp (tConstruct I 1 []) (tConstruct I 0 [])));
      ((mp, "rec"), cst (lam fx));
      ((mp, "id"), cst (lam (tRel 0)));
      ((dt, "orb"), ax);
      ((dt, "andb"), cst (lam (lam (tRel 0)))) ].

  Definition p : PAst := Untyped env (Some (tConst (mp, "main"))).
  Definition opts (std small : bool) (limit : nat) (ex : list string) : inline_opts :=
    {| inline_standard := std; inline_small := small; inline_size_limit := limit;
       inline_excluded := ex |}.

  Example standard :
    auto_inlinings (opts true false 12 []) (fun _ => false) p = [(dt, "andb")].
  Proof. vm_compute. reflexivity. Qed.

  (* No fixpoints, no computations, not the main term; oldest first. *)
  Example small :
    auto_inlinings (opts false true 12 []) (fun _ => false) p
    = [(dt, "andb"); (mp, "id"); (mp, "one"); (mp, "twice"); (mp, "four")].
  Proof. vm_compute. reflexivity. Qed.

  Example small_limit :
    auto_inlinings (opts false true 3 []) (fun _ => false) p
    = [(dt, "andb"); (mp, "id"); (mp, "one")].
  Proof. vm_compute. reflexivity. Qed.

  (* The inlined size is bounded too: [c] has size 1 and inlined size
     7 >= 2 * 3.  [d] then only receives the call to [c]. *)
  Example small_growth :
    let dup x := cst (lam (tConstruct I 0 [tConst (mp, x); tConst (mp, x)])) in
    auto_inlinings (opts false true 3 []) (fun _ => false)
      (Untyped [ ((mp, "d"), dup "c"); ((mp, "c"), dup "b"); ((mp, "b"), dup "a");
                 ((mp, "a"), cst (lam (tConstruct I 0 [tRel 0; tRel 0]))) ] None)
    = [(mp, "a"); (mp, "b"); (mp, "d")].
  Proof. vm_compute. reflexivity. Qed.

  Example excluded :
    auto_inlinings (opts false true 12 ["M.twice"; "M.id"]) (fun _ => false) p
    = [(dt, "andb"); (mp, "one"); (mp, "four")].
  Proof. vm_compute. reflexivity. Qed.

  Example remapped :
    auto_inlinings (opts true true 12 []) (eq_kername (dt, "andb")) p
    = [(mp, "id"); (mp, "one"); (mp, "twice"); (mp, "four")].
  Proof. vm_compute. reflexivity. Qed.

  Example off : auto_inlinings no_inline_opts (fun _ => false) p = [].
  Proof. reflexivity. Qed.

End AutoInliningChecks.
