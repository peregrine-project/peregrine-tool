From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From CertiRocq Require Import LambdaBoxMut.compile.
From CertiRocq Require Import LambdaBoxLocal.toplevel.
From CertiRocq Require Import LambdaANF.toplevel.
From CertiRocq Require Import Compiler.pipeline.
From CertiRocq Require Import Common.Common.
From CertiRocq Require Import Common.compM.
From CertiRocq Require Import Common.Pipeline_utils.

From ExtLib Require Import Monads.
Import MonadNotation.
Local Open Scope bs_scope.



Definition mk_opts (o : certirocq_config) : Options := {|
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

Definition mk_prims (rs : constant_remappings) : primitives :=
  map (fun '(kn, r) =>
    {| prim_name   := kn;
       prim_target := r.(re_const_s);
       prim_arity  := r.(re_const_arity);
       prim_alloc  := r.(re_const_gc);
    |}
  ) rs.

Definition get_libs (rs : constant_remappings) : IdentSet.t :=
  fold_left (fun s '(_, r) =>
    match r.(re_const_ext) with
    | Some e => IdentSet.add e s
    | _ => s
    end
  ) rs IdentSet.empty.

Definition register_prims prs (id : positive) (env : EAst.global_declarations) : pipelineM (list (primitive * positive) * positive) :=
  o <- get_options ;;
  ret (pick_prim_ident id prs).



Definition compile_program (p : EAst.program) : Program Term := {|
  main := LambdaBoxMut.compile.compile (snd p);
  env := LambdaBoxMut.compile.compile_ctx (fst p);
|}.

Definition compile_LambdaBoxMut
  : CertiRocqTrans (EAst.program) (Program LambdaBoxMut.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiRocqTrans "LambdaBoxMut" compile_program src).



Definition next_id := 100%positive.

Definition mut_pipeline prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  o <- get_options;;
  (* Translate lambda_box -> lambda_boxmut *)
  p_mut <- compile_LambdaBoxMut p;;
  check_axioms prs p_mut;;
  ret p_mut.

Definition local_pipeline prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  o <- get_options;;
  (* Translate lambda_box -> lambda_boxmut *)
  p_mut <- compile_LambdaBoxMut p;;
  check_axioms prs p_mut;;
  (* Translate lambda_boxmut -> lambda_boxlocal *)
  p_local <- compile_LambdaBoxLocal prs p_mut;;
  ret p_local.

Definition anf_pipeline' prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  o <- get_options;;
  (* Translate lambda_box -> lambda_boxmut *)
  p_mut <- compile_LambdaBoxMut p;;
  check_axioms prs p_mut;;
  (* Translate lambda_boxmut -> lambda_boxlocal *)
  p_local <- compile_LambdaBoxLocal prs p_mut;;
  (* Translate lambda_boxlocal -> lambda_anf *)
  let local_to_anf_trans := if o.(direct) then compile_LambdaANF_ANF else compile_LambdaANF_CPS in
  p_anf <- local_to_anf_trans next_id prs p_local;;
  ret p_anf.

Definition id_trans {A : Type} : CertiRocqTrans A A :=
  fun p => ret p.

Definition anf_pipeline {A : Type}
      (f : list (primitive * positive) -> CertiRocqTrans toplevel.LambdaANF_FullTerm A)
      prs
      (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
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
  f prs p_anf.
