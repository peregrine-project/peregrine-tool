(* This file provides utilises to evaluate lambda box programs *)

From Stdlib Require Import Nat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EAst.
From CertiCoq.Common Require Import Common.
From CertiCoq.Common Require Import Pipeline_utils.
From CertiCoq.LambdaBoxMut Require Import compile.
From CertiCoq.LambdaBoxMut Require Import term.
From CertiCoq.LambdaBoxMut Require Import program.
From CertiCoq.LambdaBoxMut Require Import wcbvEval.
From CertiCoq.LambdaANF Require Import toplevel.
From CertiCoq.LambdaANF Require Import eval.
From CertiCoq.LambdaANF Require Import cps.
From Peregrine Require Import CertiCoqPipeline.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

From CertiCoq.LambdaANF Require cps_show.



Section Evaluator.

  Variable (pr : prims).
  Variable (cenv : ctor_env).
  Variable (nenv : cps_show.name_env).

  Definition show_var v :=
    (cps_show.show_tree (cps_show.show_var nenv v)).

  Definition show_tag t :=
    cps_show.show_tree (cps_show.show_ftag true t).

  Definition show_tags t t' :=
    "(" ^
    show_tag t ^
    ", " ^
    show_tag t' ^
    ")".

  Fixpoint bstep_f (rho:env) (e:exp) (n:nat): exception ((env * exp) + val) :=
    match n with
    | O => exceptionMonad.Ret (inl (rho, e))
    | S n' =>
      ( match e with
        | Eprim_val x p e' =>
          let rho' := M.set x (Vprim p) rho in
          bstep_f rho' e' n'
        | Eprim x f ys e' =>
          do vs <- l_opt (get_list ys rho) ("Eprim: failed to get_list");
          do f' <- l_opt (M.get f pr) ("Eprim: prim not found");
          do v <- l_opt (f' vs) ("Eprim: prim did not compute");
          let rho' := M.set x v rho in
          bstep_f rho' e' n'
        | Econstr x t ys e' =>
          do vs <- l_opt (get_list ys rho) ("Econstr: failed to get args");
          let rho' := M.set x (Vconstr t vs) rho in
          bstep_f rho' e' n'
        | Eproj x t m y e' =>
          (match (M.get y rho) with
           | Some (Vconstr t' vs) =>
             if Pos.eqb t t' then
               do v <- l_opt (CertiCoq.LambdaANF.List_util.nthN vs m) ("Eproj: projection failed");
               let rho' := M.set x v rho in
               bstep_f rho' e' n'
             else (exceptionMonad.Exc ("Proj: tag check failed " ^ (show_tags t t')))
           | _ => (exceptionMonad.Exc ("Proj: " ^ (show_var y) ^ " var not found"))
           end)
        | Efun fl e' =>
          let rho' := def_funs fl fl rho rho in
          bstep_f rho' e' n'
        | Ehalt x =>
          match (M.get x rho) with
          | Some v => exceptionMonad.Ret (inr v)
          | None => (exceptionMonad.Exc ("Halt: " ^ (show_var x) ^ " value not found"))
          end
        | Ecase y cl =>
          match M.get y rho with
          | Some (Vconstr t vs) =>
            do e <- l_opt (findtag cl t) ("Case: " ^ (show_tag t) ^ " branch not found");
            if CertiCoq.LambdaANF.cps_util.caseConsistent_f cenv cl t then
              bstep_f rho e n'
            else (exceptionMonad.Exc "Case: consistency failure")
          | _ => (exceptionMonad.Exc ("Case: " ^ (show_var y) ^ " branch not found"))
          end
        | Eletapp x f t ys e =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("Eletapp: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e_body) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Eletapp: set_lists failed");
                  do v <- bstep_f rho'' e_body n';
                  match v with
                  | inl st => Ret (inl st)
                  | inr v => bstep_f (M.set x v rho) e n'
                  end
                else (exceptionMonad.Exc ("Eletapp: tag check failed " ^ (show_tags t t')))
              | _ => (exceptionMonad.Exc "Eletapp: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc ("Eletapp: " ^ (show_var f) ^ " bundle not found"))
           end)
        | Eapp f t ys =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("Eapp: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  bstep_f rho'' e n'
                else (exceptionMonad.Exc ("Eapp: tag check failed " ^ (show_tags t t')))
              | _ => (exceptionMonad.Exc "Eapp: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc ("Eapp: " ^ (show_var f) ^ " bundle not found"))
           end)
        end)
    end.

  Theorem bstep_f_equiv : forall n rho e v,
    bstep_f rho e n = Ret v <->
      eval.bstep_f pr cenv rho e n = Ret v.
  Proof.
    induction n; intros; try now split.
    destruct e; try apply IHn.
    - cbn.
      destruct l_opt; cbn; try now split.
      apply IHn.
    - cbn.
      destruct M.get; cbn; try now split.
      destruct v1; cbn; try now split.
      destruct findtag; cbn; try now split.
      destruct cps_util.caseConsistent_f; cbn; try now split.
      apply IHn.
    - cbn.
      destruct M.get; cbn; try now split.
      destruct v2; cbn; try now split.
      destruct Pos.eqb; cbn; try now split.
      destruct List_util.nthN; cbn; try now split.
      apply IHn.
    - cbn.
      destruct M.get; cbn; try now split.
      destruct v2; cbn; try now split.
      destruct get_list; cbn; try now split.
      destruct find_def; cbn; try now split.
      destruct p, p.
      destruct Pos.eqb; cbn; try now split.
      destruct set_lists; cbn; try now split.
      destruct bstep_f eqn:H, eval.bstep_f eqn:H1; try now split.
      + apply IHn in H1; congruence.
      + apply IHn in H; congruence.
      + cbn.
        apply IHn in H.
        rewrite H in H1.
        inversion_clear H1.
        destruct s0; cbn; try now split.
        apply IHn.
    - cbn.
      destruct M.get; cbn; try now split.
      destruct v1; cbn; try now split.
      destruct get_list; cbn; try now split.
      destruct find_def; cbn; try now split.
      destruct p, p.
      destruct Pos.eqb; cbn; try now split.
      destruct set_lists; cbn; try now split.
      apply IHn.
    - cbn.
      destruct get_list; cbn; try now split.
      destruct M.get; cbn; try now split.
      destruct (o l0); cbn; try now split.
      apply IHn.
    - cbn.
      destruct M.get; cbn; try now split.
  Qed.

  Theorem bstep_f_equiv' : forall n rho e,
    (exists s, bstep_f rho e n = Exc s) <->
      (exists s, eval.bstep_f pr cenv rho e n = Exc s).
  Proof.
    intros.
    split; intros.
    - destruct H.
      destruct bstep_f eqn:H1; try congruence.
      destruct eval.bstep_f eqn:H2; try now eexists.
      apply bstep_f_equiv in H2.
      congruence.
    - destruct H.
      destruct eval.bstep_f eqn:H1; try congruence.
      destruct bstep_f eqn:H2; try now eexists.
      apply bstep_f_equiv in H2.
      congruence.
  Qed.

End Evaluator.



Definition fuel := (2^18)%nat.

Definition eval_mut (n : nat) (p : Program Term) : pipelineM string :=
  match wcbvEval (AstCommon.env p) n (main p) with
  | Ret p => ret (print_term p)
  | Exc s => compM.failwith ("Could not evaluate program:" ^ nl ^ s)
  end.

Definition eval_anf (n : nat) (p : LambdaANF_FullTerm) : pipelineM string :=
  let (env, p) := p in
  let '(prims, _, ctor_env, _, _, nenv, _, env) := env in
  match bstep_f prims ctor_env nenv env p n with
  | Ret (inl (_, e)) => ret (cps_show.show_exp nenv ctor_env true e)
  | Ret (inr v) => ret (cps_show.show_val nenv ctor_env true v)
  | Exc s => compM.failwith ("Could not evaluate program:" ^ nl ^ s)
  end.
