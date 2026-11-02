(** * Dead-code elimination for lambda-box (unverified first cut)

    Motivation.  [EInstanceSpecialize] clones functions at statically known
    dictionaries and folds the field reads, but keeps every original
    declaration, so the dictionaries and the functions stored in them stay in
    the program.  Records of operations (mathcomp structure instances, Lean
    type-class instances) also keep every operation alive as soon as one of
    them is used.  This pass removes both kinds of dead code:

      - pruning: constants that are not reachable from the main term are
        dropped (inductives are kept);
      - field elimination: a constructor field that no [match] branch refers
        to is removed from the constructor's arity, from every application of
        the constructor, and from the binders of every branch.

    The two steps are iterated a bounded number of times, since pruning can
    make more fields unused and removing fields can make more constants
    unreachable.

    It runs in the constructors-as-blocks regime after the verified pipeline
    (no parameters, no projections: field reads are [tCase] branches), right
    after [EInstanceSpecialize].  Dropping an unused field also drops the
    evaluation of its argument; in lambda-box, which is pure, this changes no
    result of a terminating program.  The correctness of the pass is assumed,
    like that of [EInstanceSpecialize]. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst EPrimitive.
From MetaRocq.Erasure Require EGlobalEnv.
From Peregrine Require Import EDeclOrder.

Import ListNotations.

(** ** Free occurrences and strengthening *)

Fixpoint occurs (k : nat) (t : term) : bool :=
  match t with
  | tRel i => Nat.eqb i k
  | tEvar _ l => existsb (occurs k) l
  | tLambda _ b => occurs (S k) b
  | tLetIn _ b u => occurs k b || occurs (S k) u
  | tApp f a => occurs k f || occurs k a
  | tConstruct _ _ l => existsb (occurs k) l
  | tCase _ d brs =>
    occurs k d || existsb (fun br => occurs (#|fst br| + k) (snd br)) brs
  | tProj _ u => occurs k u
  | tFix defs _ | tCoFix defs _ =>
    existsb (fun d => occurs (#|defs| + k) (dbody d)) defs
  | tLazy u | tForce u => occurs k u
  | tPrim _ => true
  | _ => false
  end.

(** [lower k t] removes the binder at index [k], which must not occur in
    [t]: indices above [k] are decremented. *)
Fixpoint lower (k : nat) (t : term) : term :=
  match t with
  | tRel i => if Nat.ltb i k then tRel i else tRel (i - 1)
  | tEvar n l => tEvar n (map (lower k) l)
  | tLambda na b => tLambda na (lower (S k) b)
  | tLetIn na b u => tLetIn na (lower k b) (lower (S k) u)
  | tApp f a => tApp (lower k f) (lower k a)
  | tConstruct i n l => tConstruct i n (map (lower k) l)
  | tCase ind d brs =>
    tCase ind (lower k d) (map (fun br => (fst br, lower (#|fst br| + k) (snd br))) brs)
  | tProj p u => tProj p (lower k u)
  | tFix defs n => tFix (map (map_def (lower (#|defs| + k))) defs) n
  | tCoFix defs n => tCoFix (map (map_def (lower (#|defs| + k))) defs) n
  | tLazy u => tLazy (lower k u)
  | tForce u => tForce (lower k u)
  | tPrim p => tPrim (map_prim (lower k) p)
  | _ => t
  end.

(** ** Used fields

    A field is identified by its inductive, constructor index and position
    among the constructor's arguments. *)
Definition field := (inductive * nat * nat)%type.

Definition field_eqb (f g : field) : bool :=
  let '(i, c, j) := f in
  let '(i', c', j') := g in
  eqb i i' && Nat.eqb c c' && Nat.eqb j j'.

Fixpoint used_fields (t : term) : list field :=
  match t with
  | tEvar _ l | tConstruct _ _ l => concat (map used_fields l)
  | tLambda _ b => used_fields b
  | tLetIn _ b u | tApp b u => used_fields b ++ used_fields u
  | tCase (ind, _) d brs =>
    let in_branch c br :=
        let n := #|fst br| in
        filter (fun f => let '(_, _, j) := f in occurs (n - S j) (snd br))
               (map (fun j => (ind, c, j)) (seq 0 n)) in
    used_fields d
      ++ concat (mapi in_branch brs)
      ++ concat (map (fun br => used_fields (snd br)) brs)
  | tProj _ u | tLazy u | tForce u => used_fields u
  | tFix defs _ | tCoFix defs _ => concat (map (fun d => used_fields (dbody d)) defs)
  | tPrim _ => []
  | _ => []
  end.

Definition is_used (used : list field) (f : field) : bool :=
  existsb (field_eqb f) used.

(** ** Removing unused fields *)

(** Keep the elements of [l] at the positions [j] with [keep j]. *)
Definition filteri {A} (keep : nat -> bool) (l : list A) : list A :=
  map snd (filter (fun p => keep (fst p)) (combine (seq 0 #|l|) l)).

(** Remove the unused binders of a branch with [n] binders; field [j] is
    de Bruijn index [n - 1 - j] in the body.  Fields are processed in
    increasing [j], i.e. decreasing de Bruijn index, so earlier removals do
    not shift the indices still to be removed. *)
Definition drop_branch (keep : nat -> bool) (br : list name * term) : list name * term :=
  let n := #|fst br| in
  let body :=
      fold_left (fun body j => if keep j then body else lower (n - S j) body)
                (seq 0 n) (snd br) in
  (filteri (fun i => keep (n - S i)) (fst br), body).

Fixpoint drop_fields (used : list field) (t : term) : term :=
  let keep ind c j := is_used used (ind, c, j) in
  match t with
  | tEvar n l => tEvar n (map (drop_fields used) l)
  | tLambda na b => tLambda na (drop_fields used b)
  | tLetIn na b u => tLetIn na (drop_fields used b) (drop_fields used u)
  | tApp f a => tApp (drop_fields used f) (drop_fields used a)
  | tConstruct ind c l =>
    tConstruct ind c (filteri (keep ind c) (map (drop_fields used) l))
  | tCase (ind, np) d brs =>
    tCase (ind, np) (drop_fields used d)
          (mapi (fun c br => drop_branch (keep ind c) (fst br, drop_fields used (snd br))) brs)
  | tProj p u => tProj p (drop_fields used u)
  | tFix defs n => tFix (map (map_def (drop_fields used)) defs) n
  | tCoFix defs n => tCoFix (map (map_def (drop_fields used)) defs) n
  | tLazy u => tLazy (drop_fields used u)
  | tForce u => tForce (drop_fields used u)
  | _ => t
  end.

Definition drop_fields_mib (used : list field) (kn : kername) (mib : mutual_inductive_body)
  : mutual_inductive_body :=
  {| ind_finite := ind_finite mib;
     ind_npars := ind_npars mib;
     ind_bodies :=
       mapi (fun i oib =>
               {| ind_name := ind_name oib;
                  ind_propositional := ind_propositional oib;
                  ind_kelim := ind_kelim oib;
                  ind_ctors :=
                    mapi (fun c cb =>
                            {| cstr_name := cstr_name cb;
                               cstr_nargs :=
                                 #|filter (fun j => is_used used (mkInd kn i, c, j))
                                          (seq 0 (cstr_nargs cb))| |})
                         (ind_ctors oib);
                  ind_projs := ind_projs oib |})
            (ind_bodies mib) |}.

(** ** Reachability *)

Definition body_of (Σ : global_declarations) (kn : kername) : option term :=
  match EGlobalEnv.lookup_env Σ kn with
  | Some (ConstantDecl cb) => cst_body cb
  | _ => None
  end.

Fixpoint reachable (fuel : nat) (Σ : global_declarations) (seen : KernameSet.t)
         (todo : list kername) : KernameSet.t :=
  match fuel with
  | 0 => seen
  | S fuel =>
    match todo with
    | [] => seen
    | kn :: todo =>
      if KernameSet.mem kn seen then reachable fuel Σ seen todo else
      let next := match body_of Σ kn with Some b => consts_of b | None => [] end in
      reachable fuel Σ (KernameSet.add kn seen) (next ++ todo)
    end
  end.

Definition prune (Σ : global_declarations) (main : term) : global_declarations :=
  let fuel := S (#|Σ| * #|Σ|) in
  let live := reachable fuel Σ KernameSet.empty (consts_of main) in
  filter (fun '(kn, d) => match d with
                          | ConstantDecl _ => KernameSet.mem kn live
                          | InductiveDecl _ => true
                          end) Σ.

(** ** The pass *)

Definition dce_round (p : global_declarations * term) : global_declarations * term :=
  let '(Σ, main) := p in
  let Σ := prune Σ main in
  let used :=
      used_fields main
        ++ concat (map (fun '(_, d) => match d with
                                      | ConstantDecl cb =>
                                        match cst_body cb with Some b => used_fields b | None => [] end
                                      | _ => []
                                      end) Σ) in
  let Σ :=
      map (fun '(kn, d) =>
             (kn, match d with
                  | ConstantDecl cb =>
                    ConstantDecl {| cst_body := option_map (drop_fields used) (cst_body cb) |}
                  | InductiveDecl mib => InductiveDecl (drop_fields_mib used kn mib)
                  end)) Σ in
  (prune Σ (drop_fields used main), drop_fields used main).

Fixpoint iterate {A} (n : nat) (f : A -> A) (a : A) : A :=
  match n with 0 => a | S n => iterate n f (f a) end.

Definition dce_program (p : global_declarations * term) : global_declarations * term :=
  let '(Σ, t) := iterate 3 dce_round p in (Σ, t).

(** ** Transform wrapper (unverified, like [EInstanceSpecialize]) *)

From MetaRocq.Erasure Require Import EWellformed EWcbvEval EProgram.
From MetaRocq.Common Require Import Transform.

Axiom trust_dce_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (dce_program input).

Axiom trust_dce_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term) (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term, eval_eprogram wfl (dce_program p) v'.

Import Transform.

Program Definition dce_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "dead-code elimination";
     transform p _ := dce_program p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := True |}.
Next Obligation.
  now apply trust_dce_wf.
Qed.
Next Obligation.
  edestruct trust_dce_pres as [v' Hv']; eauto.
Qed.
