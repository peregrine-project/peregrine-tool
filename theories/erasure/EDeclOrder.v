(** Dependency order of a λ□ environment.

    CertiRocq translates the environment in order and rejects a declaration
    that refers to one placed after it ("Unknown DeBruijn index").  A pass that
    adds declarations ([EInstanceSpecialize]) re-establishes the order with
    [topo_sort]: newest first, every declaration before what it refers to. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst EPrimitive.
From MetaRocq.Erasure Require EGlobalEnv.

Import ListNotations.

Fixpoint consts_of (t : term) : list kername :=
  match t with
  | tConst kn => [kn]
  | tEvar _ l | tConstruct _ _ l => concat (map consts_of l)
  | tLambda _ b => consts_of b
  | tLetIn _ b u | tApp b u => consts_of b ++ consts_of u
  | tCase _ d brs => consts_of d ++ concat (map (fun br => consts_of (snd br)) brs)
  | tProj _ u | tLazy u | tForce u => consts_of u
  | tFix defs _ | tCoFix defs _ => concat (map (fun d => consts_of (dbody d)) defs)
  | _ => []
  end.

Fixpoint inds_of (t : term) : list kername :=
  match t with
  | tConstruct ind _ l => inductive_mind ind :: concat (map inds_of l)
  | tCase (ind, _) d brs =>
    inductive_mind ind :: inds_of d ++ concat (map (fun br => inds_of (snd br)) brs)
  | tEvar _ l => concat (map inds_of l)
  | tLambda _ b => inds_of b
  | tLetIn _ b u | tApp b u => inds_of b ++ inds_of u
  | tProj _ u | tLazy u | tForce u => inds_of u
  | tFix defs _ | tCoFix defs _ => concat (map (fun d => inds_of (dbody d)) defs)
  | _ => []
  end.

Definition deps_of (d : global_decl) : list kername :=
  match d with
  | ConstantDecl cb =>
    match cst_body cb with Some b => consts_of b ++ inds_of b | None => [] end
  | InductiveDecl _ => []
  end.

(** Depth-first: dependencies are pushed before the declaration, so the
    accumulator is newest first. *)
Fixpoint visit (fuel : nat) (Σ : global_declarations) (st : KernameSet.t * global_declarations)
         (kn : kername) : KernameSet.t * global_declarations :=
  match fuel with
  | 0 => st
  | S fuel =>
    let '(seen, acc) := st in
    if KernameSet.mem kn seen then st else
    match EGlobalEnv.lookup_env Σ kn with
    | None => st
    | Some d =>
      let '(seen, acc) := fold_left (visit fuel Σ) (deps_of d) (KernameSet.add kn seen, acc) in
      (seen, (kn, d) :: acc)
    end
  end.

Definition topo_sort (Σ : global_declarations) : global_declarations :=
  snd (fold_left (fun st '(kn, _) => visit (S #|Σ|) Σ st kn) (List.rev Σ)
                 (KernameSet.empty, [])).
