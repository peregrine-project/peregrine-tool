(** * Lambda Calculus Interpreter Benchmark

    A simple untyped lambda calculus interpreter using de Bruijn indices.
    Demonstrates closures, environments, and evaluation.
*)

From Stdlib Require Import List Arith ZArith.
Import ListNotations.

(** Lambda terms with de Bruijn indices *)
Inductive term : Type :=
  | Var : nat -> term                    (* variable (de Bruijn index) *)
  | Lam : term -> term                   (* lambda abstraction *)
  | App : term -> term -> term           (* application *)
  | Lit : Z -> term                      (* integer literal *)
  | Add : term -> term -> term           (* addition *)
  | Mul : term -> term -> term           (* multiplication *)
  | IfZ : term -> term -> term -> term.  (* if zero then else *)

(** Values *)
Inductive value : Type :=
  | VInt : Z -> value
  | VClosure : list value -> term -> value.  (* environment, body *)

(** Environment lookup *)
Fixpoint lookup (n : nat) (env : list value) : option value :=
  match n, env with
  | O, v :: _ => Some v
  | S n', _ :: env' => lookup n' env'
  | _, [] => None
  end.

(** Evaluation with fuel *)
Fixpoint eval_fuel (fuel : nat) (env : list value) (t : term) : option value :=
  match fuel with
  | O => None  (* Out of fuel *)
  | S fuel' =>
      match t with
      | Var n => lookup n env
      | Lam body => Some (VClosure env body)
      | App f arg =>
          match eval_fuel fuel' env f with
          | Some (VClosure env' body) =>
              match eval_fuel fuel' env arg with
              | Some v => eval_fuel fuel' (v :: env') body
              | None => None
              end
          | _ => None
          end
      | Lit n => Some (VInt n)
      | Add e1 e2 =>
          match eval_fuel fuel' env e1, eval_fuel fuel' env e2 with
          | Some (VInt n1), Some (VInt n2) => Some (VInt (n1 + n2)%Z)
          | _, _ => None
          end
      | Mul e1 e2 =>
          match eval_fuel fuel' env e1, eval_fuel fuel' env e2 with
          | Some (VInt n1), Some (VInt n2) => Some (VInt (n1 * n2)%Z)
          | _, _ => None
          end
      | IfZ cond then_ else_ =>
          match eval_fuel fuel' env cond with
          | Some (VInt 0%Z) => eval_fuel fuel' env then_
          | Some (VInt _) => eval_fuel fuel' env else_
          | _ => None
          end
      end
  end.

Definition eval (t : term) : option value :=
  eval_fuel 10000 [] t.

(** Extract integer from value *)
Definition to_int (v : option value) : Z :=
  match v with
  | Some (VInt n) => n
  | _ => 0%Z
  end.

(** Church numerals *)
Definition church_zero : term := Lam (Lam (Var 0)).  (* λf. λx. x *)
Definition church_succ : term :=
  Lam (Lam (Lam (App (Var 1) (App (App (Var 2) (Var 1)) (Var 0))))).
  (* λn. λf. λx. f (n f x) *)

Definition church_add : term :=
  Lam (Lam (Lam (Lam (App (App (Var 3) (Var 1)) (App (App (Var 2) (Var 1)) (Var 0)))))).
  (* λm. λn. λf. λx. m f (n f x) *)

(** Build Church numeral n *)
Fixpoint church_num (n : nat) : term :=
  match n with
  | O => church_zero
  | S n' => App church_succ (church_num n')
  end.

(** Convert Church numeral to integer *)
Definition church_to_int : term :=
  Lam (App (App (Var 0) (Lam (Add (Var 0) (Lit 1)))) (Lit 0)).
  (* λn. n (λx. x + 1) 0 *)

(** Factorial using Y combinator style (with explicit recursion) *)
Fixpoint make_fact_aux (fuel : nat) : term :=
  match fuel with
  | O => Lit 1
  | S fuel' =>
      Lam (IfZ (Var 0)
               (Lit 1)
               (Mul (Var 0) (App (make_fact_aux fuel') (Add (Var 0) (Lit (-1)%Z)))))
  end.

Definition factorial_term : term := make_fact_aux 20.

(** Test: (λx. x + 1) 5 = 6 *)
Definition test_simple : Z := to_int (eval (App (Lam (Add (Var 0) (Lit 1))) (Lit 5))).

(** Test: factorial *)
Definition test_fact_5 : Z := to_int (eval (App factorial_term (Lit 5))).

(** Benchmark: evaluate factorial *)
Definition lambda_interp_bench (n : Z) : Z :=
  to_int (eval (App factorial_term (Lit n))).

(** Benchmark: Church numeral addition *)
Definition church_bench (n : nat) : Z :=
  let cn := church_num n in
  let add_nn := App (App church_add cn) cn in
  to_int (eval (App church_to_int add_nn)).
