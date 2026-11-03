From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From CertiRocq Require Import LambdaANF.toplevel.
From CertiRocq Require Import Compiler.pipeline.
From CertiRocq Require Import Common.Common.
From CertiRocq Require Import Common.compM.
From CertiRocq Require Import Common.Pipeline_utils.
From MetaRocq.Erasure Require EImplementBox.

From ExtLib Require Import Monads.
Import MonadNotation.
Local Open Scope bs_scope.



Definition mk_opts (o : certirocq_config) : Options := {|
  erasure_config := Erasure.default_erasure_config; (* Not used *)
  inductives_mapping := []; (* Not used *)
  direct := o.(Config.direct);
  c_args := o.(Config.c_args);
  anf_variant := 0;
  show_anf := false;
  o_level := o.(Config.o_level);
  time := false;
  time_anf := false;
  debug := false;
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



Definition next_id := 100%positive.

(* A program without a main term gets [tBox] as its main ([PAst_to_EAst]),
   after the middle-end has implemented boxes. CertiRocq's CPS conversion
   rejects [tBox], so it gets the implementation of box instead. *)
Definition implement_main_box (p : EAst.program) : EAst.program :=
  match p.2 with
  | EAst.tBox => (p.1, EImplementBox.iBox)
  | _ => p
  end.

Definition compile_LambdaBox_to_LambdaANF (direct : bool) next_id prs (p : EAst.program) :=
  if direct then compile_LambdaANF_ANF next_id prs p
  else compile_LambdaANF_CPS next_id prs (implement_main_box p).

Definition anf_pipeline' prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  o <- get_options;;
  check_axioms prs p;;
  (* Translate lambda_box -> lambda_anf *)
  p_anf <- compile_LambdaBox_to_LambdaANF o.(direct) next_id prs p;;
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
  check_axioms prs p;;
  (* Translate lambda_box -> lambda_anf *)
  p_anf <- compile_LambdaBox_to_LambdaANF o.(direct) next_id prs p;;
  (* Translate lambda_anf -> lambda_anf *)
  let anf_trans :=
    if o.(debug)
    then compile_LambdaANF_debug (* For debugging intermediate states of the λanf pipeline *)
    else compile_LambdaANF in
  p_anf <- anf_trans next_id p_anf;;
  f prs p_anf.
