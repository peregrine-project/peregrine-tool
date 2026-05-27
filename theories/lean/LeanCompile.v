From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import LeanIR.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  EAst (λ_□) → LeanIR translation                                   *)
(*                                                                    *)
(*  The context [ctx] maps de Bruijn indices to the [lterm] that      *)
(*  should be emitted for [tRel n].  Ordinary binders push [LVar id]; *)
(*  a recursive top-level [tFix] self-reference pushes [LConst kn].   *)
(* ------------------------------------------------------------------ *)

Definition ctx := list lterm.

Definition lookup_rel (c : ctx) (n : nat) : lterm :=
  nth n c (LPanic ("free de Bruijn index " ++ string_of_nat n)).

(* Produce an ident from a binder name.  Anonymous binders get a name
   derived from the current depth so they remain unique within scope. *)
Definition ident_of_name (depth : nat) (n : name) : ident :=
  match n with
  | nNamed s => s ++ "_" ++ string_of_nat depth
  | nAnon    => "_p" ++ string_of_nat depth
  end.

(* Peel top-level [tLambda]s off [t], collecting the binder names. *)
Fixpoint peel_lambdas (t : EAst.term) : list name * EAst.term :=
  match t with
  | EAst.tLambda na body =>
    let (nas, body') := peel_lambdas body in
    (na :: nas, body')
  | _ => ([], t)
  end.

(* Allocate fresh idents for a [list name], assigning each binder the
   depth it ends up at after the (left-to-right) sequence of pushes
   onto the existing context of depth [base]. *)
Fixpoint generate_ids (base : nat) (ns : list name) : list ident :=
  match ns with
  | [] => []
  | n :: rest => ident_of_name base n :: generate_ids (S base) rest
  end.

(* Push a list of idents (in left-to-right binding order) as [LVar]s onto
   the context.  The leftmost binder ends up deepest. *)
Fixpoint push_vars (ids : list ident) (c : ctx) : ctx :=
  match ids with
  | [] => c
  | id :: rest => push_vars rest (LVar id :: c)
  end.

Fixpoint compile_term (c : ctx) (t : EAst.term) {struct t} : lterm :=
  match t with
  | EAst.tBox => LPanic "tBox should have been erased by implement_box"
  | EAst.tRel n => lookup_rel c n
  | EAst.tVar i => LVar i
  | EAst.tEvar _ _ => LPanic "tEvar unsupported"
  | EAst.tLambda na body =>
    let id := ident_of_name (List.length c) na in
    LLam id (compile_term (LVar id :: c) body)
  | EAst.tLetIn na b body =>
    let id := ident_of_name (List.length c) na in
    LLet id (compile_term c b) (compile_term (LVar id :: c) body)
  | EAst.tApp u v =>
    LApp (compile_term c u) (compile_term c v)
  | EAst.tConst kn => LConst kn
  | EAst.tConstruct ind n args =>
    LCtor ind n (List.map (compile_term c) args)
  | EAst.tCase indn discr brs =>
    let ind := fst indn in
    let discr' := compile_term c discr in
    let brs' := List.map (fun '(ns, body) =>
      let ids := generate_ids (List.length c) ns in
      let c' := push_vars ids c in
      (ids, compile_term c' body)
    ) brs in
    LCase discr' ind brs'
  | EAst.tProj p discr =>
    LProj p (compile_term c discr)
  | EAst.tFix _ _ =>
    LPanic "nested tFix not yet supported"
  | EAst.tCoFix _ _ =>
    LPanic "tCoFix unsupported"
  | EAst.tPrim _ =>
    LPanic "tPrim unsupported"
  | EAst.tLazy _ =>
    LPanic "tLazy should have been removed by implement_lazy"
  | EAst.tForce _ =>
    LPanic "tForce should have been removed by implement_lazy"
  end.

(* Compile the body of a single top-level constant.

   Common shapes handled specially:
   - [tLambda x .. body]: peel into [lfun_params]
   - [tFix [d] 0]: self-recursive singleton; bind the fix variable to
     [LConst kn] so recursive calls re-enter through the global name *)
Definition compile_constant_body (kn : kername) (t : EAst.term) : lfun :=
  let (outer_params, body1) := peel_lambdas t in
  match body1 with
  | EAst.tFix [d] 0 =>
    let inner := d.(EAst.dbody) in
    let (inner_params, body2) := peel_lambdas inner in
    let all_params := List.app outer_params inner_params in
    let ids := generate_ids 0 all_params in
    let n_outer := List.length outer_params in
    let outer_ids := List.firstn n_outer ids in
    let inner_ids := List.skipn n_outer ids in
    let c0 : ctx := push_vars outer_ids [] in
    let c1 : ctx := LConst kn :: c0 in
    let c2 : ctx := push_vars inner_ids c1 in
    {| lfun_params := ids;
       lfun_body   := compile_term c2 body2 |}
  | _ =>
    let ids := generate_ids 0 outer_params in
    let c := push_vars ids [] in
    {| lfun_params := ids;
       lfun_body   := compile_term c body1 |}
  end.

Definition compile_decl (kn : kername) (gd : EAst.global_decl) : option ldecl :=
  match gd with
  | EAst.ConstantDecl cb =>
    match cb.(EAst.cst_body) with
    | None => None  (* axiom; skip *)
    | Some t => Some (LDef (compile_constant_body kn t))
    end
  | EAst.InductiveDecl mib => Some (LInductive mib)
  end.

Definition compile_env (env : EAst.global_declarations) : list (kername * ldecl) :=
  List.fold_right (fun '(kn, gd) acc =>
    match compile_decl kn gd with
    | Some d => (kn, d) :: acc
    | None => acc
    end
  ) [] env.

(* MetaCoq stores the global environment in reverse order of dependency
   (most recently declared first).  Lean wants definitions before uses,
   so we reverse. *)
Definition compile_program (p : EAst.program) : lprogram :=
  let env := List.rev (fst p) in
  {| ldecls := compile_env env |}.
