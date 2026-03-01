From MetaRocq.Erasure Require EAst.
From CertiCoq Require Import LambdaBoxMut.compile.
From CertiCoq Require Import LambdaBoxLocal.toplevel.
From CertiCoq Require Import LambdaANF.toplevel.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Common.
From CertiCoq Require Import Common.compM.
From CertiCoq Require Import Common.Pipeline_utils.
From ExtLib.Structures Require Import Monad.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.

Import ListNotations.
Import Monads.
Import MonadNotation.



Definition make_opts (cps debug : bool) : Options :=
  {| erasure_config := Erasure.default_erasure_config;
     inductives_mapping := [];
     direct := negb cps;
     c_args := 5;
     anf_conf := 0;
     show_anf := false;
     o_level := 0;
     time := false;
     time_anf := false;
     debug := debug;
     dev := 0;
     Pipeline_utils.prefix := "";
     Pipeline_utils.body_name := "body";
     prims := [];
  |}.

Fixpoint find_arity (tau : EAst.term) : nat :=
  match tau with
  | EAst.tLambda na body => 1 + find_arity body
  | _ => 0
  end.

Definition find_global_decl_arity (gd : EAst.global_decl) : error nat :=
  match gd with
  | EAst.ConstantDecl bd =>
    match (EAst.cst_body bd) with
    | Some bd => Ret (find_arity bd)
    | None => Err ("Found empty ConstantDecl body")
    end
  | EAst.InductiveDecl _ => Err ("Expected ConstantDecl but found InductiveDecl")
  end.

Fixpoint find_prim_arity (env : EAst.global_declarations) (pr : kername) : error nat :=
  match env with
  | [] => Err ("Constant " ++ string_of_kername pr ++ " not found in environment")
  | (n, gd) :: env =>
    if eq_kername pr n then find_global_decl_arity gd
    else find_prim_arity env pr
  end.

Fixpoint find_prim_arities (env : EAst.global_declarations) (prs : list (kername * string * bool)) : error (list (kername * string * bool * nat * positive)) :=
  match prs with
  | [] => Ret []
  | ((pr, s), b) :: prs =>
    match find_prim_arity env pr with
    | Err _ => (* Be lenient, if a declared primitive is not part of the environment, just skip it *)
      prs' <- find_prim_arities env prs ;;
      Ret prs'
    | Ret arity =>
      prs' <- find_prim_arities env prs ;;
      Ret ((pr, s, b, arity, 1%positive) :: prs')
    end
  end.

Definition register_prims (id : positive) (env : EAst.global_declarations) : pipelineM (list (kername * string * bool * nat * positive) * positive) :=
  o <- get_options ;;
  match find_prim_arities env (prims o) with
  | Ret prs =>
    ret (pick_prim_ident id prs)
  | Err s => failwith s
  end.


Definition anf_pipeline (p : EAst.program) prs next_id :=
  o <- get_options ;;
  (* Translate lambda_box -> lambda_boxmut *)
  let p_mut := {| CertiCoq.Common.AstCommon.main := LambdaBoxMut.compile.compile (snd p) ; CertiCoq.Common.AstCommon.env := LambdaBoxMut.compile.compile_ctx (fst p) |} in
  check_axioms prs p_mut;;
  (* Translate lambda_boxmut -> lambda_boxlocal *)
  p_local <- compile_LambdaBoxLocal prs p_mut;;
  (* Translate lambda_boxlocal -> lambda_anf *)
  let local_to_anf_trans := if direct o then compile_LambdaANF_ANF else compile_LambdaANF_CPS in
  p_anf <- local_to_anf_trans next_id prs p_local;;
  (* Translate lambda_anf -> lambda_anf *)
  let anf_trans := if debug o then compile_LambdaANF_debug (* For debugging intermediate states of the λanf pipeline *) else compile_LambdaANF in
  p_anf <- anf_trans next_id p_anf;;
  ret p_anf.

Definition show_IR (opts : Options) (p : EAst.program) : (error string * string) :=
  (* For simplicity we assume that the program contains no primitives *)
  let next_id := 100%positive in
  let genv := fst p in
  let ir_term p :=
    o <- get_options;;
    '(prs, next_id) <- register_prims next_id genv;;
    anf_pipeline p prs next_id in
  let (perr, log) := run_pipeline _ _ opts p ir_term in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (Ret (cps_show.show_exp nenv cenv true e), log)
  | Err s => (Err s, log)
  end.
