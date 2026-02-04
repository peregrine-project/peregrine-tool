From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From CertiCoq Require Import LambdaBoxMut.compile.
From CertiCoq Require Import LambdaBoxLocal.toplevel.
From CertiCoq Require Import LambdaANF.toplevel.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Common.
From CertiCoq Require Import Common.compM.
From CertiCoq Require Import Common.Pipeline_utils.

From ExtLib Require Import Monads.
Import MonadNotation.
Local Open Scope bs_scope.



Definition mk_opts (o : certicoq_config) : Options := {|
  erasure_config := Erasure.default_erasure_config; (* Not used *)
  inductives_mapping := []; (* Not used *)
  direct := o.(Config.direct);
  c_args := o.(Config.c_args);
  anf_conf := 0;
  show_anf := false;
  o_level := o.(Config.o_level);
  time := false;
  time_anf := false;
  debug := false;
  dev := 0;
  Pipeline_utils.prefix := o.(Config.prefix);
  Pipeline_utils.body_name := o.(Config.body_name);
  prims := []; (* We pass prims directly to the pipeline *)
|}.

Definition mk_prims (rs : remappings) : list (((kername × string) × arity) × bool) :=
  Utils.filter_map (fun x =>
    match x with
    | RemapConstant kn _ a gc s =>
      Some (kn, s, a, gc)
    | _ => None
    end
  ) rs.

Definition get_libs (rs : remappings) : IdentSet.t :=
  fold_left (fun s r =>
    match r with
    | RemapConstant _ (Some e) _ _ _ => IdentSet.add e s
    | _ => s
    end
  ) rs IdentSet.empty.



Fixpoint find_arity (tau : EAst.term) : nat :=
  match tau with
  | EAst.tLambda _ body => 1 + find_arity body
  | _ => 0
  end.

Definition find_global_decl_arity (gd : EAst.global_decl) : error nat :=
  match gd with
  | EAst.ConstantDecl bd =>
    match (EAst.cst_body bd) with
    | Some bd => Ret (find_arity bd)
    | None => Err ("Found empty ConstantDecl body") (* TODO *)
    end
  | EAst.InductiveDecl _ =>
    Err ("Expected ConstantDecl but found InductiveDecl")
  end.

Fixpoint find_prim_arity (env : EAst.global_declarations) (pr : kername) : error nat :=
  match env with
  | [] => Err ("Constant " ++ string_of_kername pr ++ " not found in environment")
  | (n, gd) :: env =>
    if eq_kername pr n then find_global_decl_arity gd
    else find_prim_arity env pr
  end.

Fixpoint find_prim_arities (env : EAst.global_declarations) (prs : list (kername * string * arity * bool)) : error (list (kername * string * bool * nat * positive)) :=
  match prs with
  | [] => Ret []
  | (pr, s, Some a, b) :: prs =>
    prs' <- find_prim_arities env prs ;;
    Ret ((pr, s, b, a, 1%positive) :: prs')
  | (pr, s, None, b) :: prs =>
    match find_prim_arity env pr with
    | Err _ => (* Be lenient, if a declared primitive is not part of the environment, just skip it *)
      prs' <- find_prim_arities env prs ;;
      Ret prs'
    | Ret arity =>
      prs' <- find_prim_arities env prs ;;
      Ret ((pr, s, b, arity, 1%positive) :: prs')
    end
  end.

Definition register_prims prs (id : positive) (env : EAst.global_declarations) : pipelineM (list (kername * string * bool * nat * positive) * positive) :=
  match find_prim_arities env prs with
  | Ret prs =>
    ret (pick_prim_ident id prs)
  | Err s => failwith s
  end.



Definition compile_program (p : EAst.program) : Program Term := {|
  main := LambdaBoxMut.compile.compile (snd p);
  env := LambdaBoxMut.compile.compile_ctx (fst p);
|}.

Definition compile_LambdaBoxMut
  : CertiCoqTrans (EAst.program) (Program LambdaBoxMut.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiCoqTrans "LambdaBoxMut" compile_program src).



Definition next_id := 100%positive.

Definition anf_pipeline (p : EAst.program) prs next_id :=
  o <- get_options;;
  (* Translate lambda_box -> lambda_boxmut *)
  p_mut <- compile_LambdaBoxMut p;;
  check_axioms prs p_mut;;
  (* Translate lambda_boxmut -> lambda_boxlocal *)
  p_local <- compile_LambdaBoxLocal prs p_mut;;
  (* Translate lambda_boxlocal -> lambda_anf *)
  let local_to_anf_trans := if o.(direct) then compile_LambdaANF_ANF else compile_LambdaANF_CPS in
  p_anf <- local_to_anf_trans next_id prs p_local;;
  (* Translate lambda_anf -> lambda_anf *)
  let anf_trans :=
    if o.(debug)
    then compile_LambdaANF_debug (* For debugging intermediate states of the λanf pipeline *)
    else compile_LambdaANF in
  p_anf <- anf_trans next_id p_anf;;
  ret p_anf.
