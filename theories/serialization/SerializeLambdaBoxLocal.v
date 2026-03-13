From CertiRocq Require Import AstCommon.
From CertiRocq.LambdaBoxLocal Require Import LambdaBoxMut_to_LambdaBoxLocal.
From CertiRocq.LambdaBoxLocal Require Import expression.
From CertiRocq.LambdaBoxLocal Require toplevel.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From Stdlib Require Import NArith.
From CeresBS Require Import Ceres.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeLambdaBoxMut.

Import ListNotations.
Local Open Scope bs_scope.



Instance Serialize_dcon : Serialize dcon :=
  to_sexp.



Fixpoint exps_to_list (l : exps) : list exp :=
  match l with
  | enil => []
  | econs e es => e :: exps_to_list es
  end.

Fixpoint exps_of_list (l : list exp) : exps :=
  match l with
  | [] => enil
  | e :: es => econs e (exps_of_list es)
  end.

Fixpoint efnlst_to_list (l : efnlst) : list (name * exp) :=
  match l with
  | eflnil => []
  | eflcons n e es => (n, e) :: efnlst_to_list es
  end.

Fixpoint efnlst_of_list (l : list (name * exp)) : efnlst :=
  match l with
  | [] => eflnil
  | (n,e) :: es => eflcons n e (efnlst_of_list es)
  end.

Fixpoint branches_e_to_list (l : branches_e) : list (dcon * (N * list name) * exp) :=
  match l with
  | brnil_e => []
  | brcons_e n t i ts => (n, t, i) :: branches_e_to_list ts
  end.

Fixpoint branches_e_of_list (l : list (dcon * (N * list name) * exp)) : branches_e :=
  match l with
  | [] => brnil_e
  | (n,t,i) :: ts => brcons_e n t i (branches_e_of_list ts)
  end.

#[bypass_check(guard)]
Definition Serialize_exp_aux : Serialize exp :=
  fix sz e {struct e} :=
    match e with
    | Var_e n => [Atom "Var_e"; to_sexp n]
    | Lam_e n e => [Atom "Lam_e"; to_sexp n; sz e]
    | App_e e1 e2 => [Atom "App_e"; sz e1; sz e2]
    | Con_e d es => [Atom "Con_e"; to_sexp d; @Serialize_list _ sz (exps_to_list es)]
    | Match_e e n brs =>
      [ Atom "Match_e";
        sz e;
        to_sexp n;
        @Serialize_list _
          (@Serialize_product _ _ _ sz)
          (branches_e_to_list brs)
      ]
    | Let_e n e1 e2 => [Atom "Let_e"; to_sexp n; sz e1; sz e2]
    | Fix_e es n =>
      [ Atom "Fix_e";
        @Serialize_list _
          (@Serialize_product _ _ _ sz)
          (efnlst_to_list es);
        to_sexp n
      ]
    | Prf_e => Atom "Prf_e"
    | Prim_val_e p => [Atom "Prim_val_e"; to_sexp p]
    | Prim_e i => [Atom "Prim_e"; to_sexp i]
    end%sexp.

Instance Serialize_exp : Serialize exp :=
  Serialize_exp_aux.

Instance Serialize_ienv : Serialize ienv :=
  to_sexp.

Instance Serialize_LambdaBoxLocalTerm : Serialize toplevel.LambdaBoxLocalTerm :=
  to_sexp.



Definition string_of_dcon (x : dcon) : string :=
  @to_string dcon Serialize_dcon x.

Definition string_of_exp (x : exp) : string :=
  @to_string exp Serialize_exp x.

Definition string_of_ienv (x : ienv) : string :=
  @to_string ienv Serialize_ienv x.

Definition string_of_LambdaBoxLocalTerm (x : toplevel.LambdaBoxLocalTerm) : string :=
  @to_string toplevel.LambdaBoxLocalTerm Serialize_LambdaBoxLocalTerm x.
