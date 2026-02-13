From MetaRocq.Erasure Require EAst.
From MetaRocq.Common Require Import Kernames.
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
From MetaRocq.Utils Require Import bytestring.

Import ListNotations.
Import Monads.
Import MonadNotation.

Open Scope bs_scope.

(* Uint63 primitive kernel names *)
Definition int63_mod : modpath := MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Corelib"].

Definition mk_int63_kn (s : ident) : kername := (int63_mod, s).

(* Uint63 primitive mappings: (kername, c_function_name, needs_tinfo, arity)
   Arities are hardcoded since EAst doesn't have type information for primitives *)
Definition int63_prims_with_arity : list (kername * bytestring.string * bool * nat) :=
  [ (* The int type itself - mapped to primint type, arity 0 *)
    (mk_int63_kn "int"%bs, "primint"%bs, false, 0);
    (* Binary arithmetic operations - arity 2 *)
    (mk_int63_kn "add"%bs, "prim_int63_add"%bs, false, 2);
    (mk_int63_kn "sub"%bs, "prim_int63_sub"%bs, false, 2);
    (mk_int63_kn "mul"%bs, "prim_int63_mul"%bs, false, 2);
    (mk_int63_kn "div"%bs, "prim_int63_div"%bs, false, 2);
    (mk_int63_kn "mod"%bs, "prim_int63_mod"%bs, false, 2);
    (* Binary bitwise operations - arity 2 *)
    (mk_int63_kn "lsl"%bs, "prim_int63_lsl"%bs, false, 2);
    (mk_int63_kn "lsr"%bs, "prim_int63_lsr"%bs, false, 2);
    (mk_int63_kn "land"%bs, "prim_int63_land"%bs, false, 2);
    (mk_int63_kn "lor"%bs, "prim_int63_lor"%bs, false, 2);
    (mk_int63_kn "lxor"%bs, "prim_int63_lxor"%bs, false, 2);
    (* Binary comparison operations - arity 2 *)
    (mk_int63_kn "eqb"%bs, "prim_int63_eqb"%bs, false, 2);
    (mk_int63_kn "ltb"%bs, "prim_int63_ltb"%bs, false, 2);
    (mk_int63_kn "leb"%bs, "prim_int63_leb"%bs, false, 2);
    (mk_int63_kn "compare"%bs, "prim_int63_compare"%bs, false, 2);
    (* Unary operations - arity 1 *)
    (mk_int63_kn "head0"%bs, "prim_int63_head0"%bs, false, 1);
    (mk_int63_kn "tail0"%bs, "prim_int63_tail0"%bs, false, 1);
    (* Binary operations that allocate - arity 2, need tinfo *)
    (mk_int63_kn "addc"%bs, "prim_int63_addc"%bs, true, 2);
    (mk_int63_kn "addcarryc"%bs, "prim_int63_addcarryc"%bs, true, 2);
    (mk_int63_kn "subc"%bs, "prim_int63_subc"%bs, true, 2);
    (mk_int63_kn "subcarryc"%bs, "prim_int63_subcarryc"%bs, true, 2);
    (mk_int63_kn "mulc"%bs, "prim_int63_mulc"%bs, true, 2);
    (mk_int63_kn "diveucl"%bs, "prim_int63_diveucl"%bs, true, 2);
    (* Ternary operations - arity 3 *)
    (mk_int63_kn "diveucl_21"%bs, "prim_int63_diveucl_21"%bs, true, 3);
    (mk_int63_kn "addmuldiv"%bs, "prim_int63_addmuldiv"%bs, false, 3)
  ].

(* Strip arities for Options.prims which expects (kername * string * bool) *)
Definition int63_prims : list (kername * bytestring.string * bool) :=
  map (fun '(kn, s, b, _) => (kn, s, b)) int63_prims_with_arity.

(* Lookup hardcoded arity for a primitive *)
Fixpoint lookup_prim_arity (prims : list (kername * bytestring.string * bool * nat)) (kn : kername) : option nat :=
  match prims with
  | [] => None
  | (kn', _, _, arity) :: rest =>
    if eq_kername kn kn' then Some arity
    else lookup_prim_arity rest kn
  end.

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
     prims := int63_prims;
  |}.

Fixpoint find_arity (tau : EAst.term) : nat :=
  match tau with
  | EAst.tLambda na body => 1 + find_arity body
  | _ => 0
  end.

(* Find arity from global decl, with fallback to hardcoded arities for primitives *)
Definition find_global_decl_arity (kn : kername) (gd : EAst.global_decl) : error nat :=
  match gd with
  | EAst.ConstantDecl bd =>
    match (EAst.cst_body bd) with
    | Some bd => Ret (find_arity bd)
    | None =>
      (* Primitive with no body - use hardcoded arity if available *)
      match lookup_prim_arity int63_prims_with_arity kn with
      | Some arity => Ret arity
      | None => Err ("Found empty ConstantDecl body for " ++ string_of_kername kn)
      end
    end
  | EAst.InductiveDecl _ => Err ("Expected ConstantDecl but found InductiveDecl")
  end.

Fixpoint find_prim_arity (env : EAst.global_declarations) (pr : kername) : error nat :=
  match env with
  | [] => Err ("Constant " ++ string_of_kername pr ++ " not found in environment")
  | (n, gd) :: env =>
    if eq_kername pr n then find_global_decl_arity pr gd
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
