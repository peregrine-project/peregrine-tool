(** * Symbolic Differentiation Benchmark

    Symbolic differentiation of algebraic expressions.
    Classic functional programming example showcasing ADTs and pattern matching.
*)

From Stdlib Require Import ZArith List.
Import ListNotations.

Open Scope Z_scope.

(** Expression type *)
Inductive expr : Type :=
  | Const : Z -> expr                (* constant *)
  | Var : expr                       (* variable x *)
  | Add : expr -> expr -> expr       (* e1 + e2 *)
  | Sub : expr -> expr -> expr       (* e1 - e2 *)
  | Mul : expr -> expr -> expr       (* e1 * e2 *)
  | Div : expr -> expr -> expr       (* e1 / e2 *)
  | Pow : expr -> Z -> expr          (* e ^ n *)
  | Ln : expr -> expr                (* ln(e) *)
  | Exp : expr -> expr.              (* e^x *)

(** Symbolic differentiation with respect to x *)
Fixpoint diff (e : expr) : expr :=
  match e with
  | Const _ => Const 0
  | Var => Const 1
  | Add e1 e2 => Add (diff e1) (diff e2)
  | Sub e1 e2 => Sub (diff e1) (diff e2)
  | Mul e1 e2 => Add (Mul (diff e1) e2) (Mul e1 (diff e2))  (* product rule *)
  | Div e1 e2 => Div (Sub (Mul (diff e1) e2) (Mul e1 (diff e2)))
                     (Mul e2 e2)  (* quotient rule *)
  | Pow e n => Mul (Mul (Const n) (Pow e (n - 1))) (diff e)  (* power rule *)
  | Ln e => Div (diff e) e  (* chain rule *)
  | Exp e => Mul (Exp e) (diff e)  (* chain rule *)
  end.

(** Simplify expressions *)
Fixpoint simplify_fuel (fuel : nat) (e : expr) : expr :=
  match fuel with
  | O => e
  | S fuel' =>
      let e' :=
        match e with
        | Add (Const 0) e2 => simplify_fuel fuel' e2
        | Add e1 (Const 0) => simplify_fuel fuel' e1
        | Add (Const a) (Const b) => Const (a + b)
        | Sub e1 (Const 0) => simplify_fuel fuel' e1
        | Sub (Const a) (Const b) => Const (a - b)
        | Mul (Const 0) _ => Const 0
        | Mul _ (Const 0) => Const 0
        | Mul (Const 1) e2 => simplify_fuel fuel' e2
        | Mul e1 (Const 1) => simplify_fuel fuel' e1
        | Mul (Const a) (Const b) => Const (a * b)
        | Div e1 (Const 1) => simplify_fuel fuel' e1
        | Pow _ 0 => Const 1
        | Pow e 1 => simplify_fuel fuel' e
        | Add e1 e2 => Add (simplify_fuel fuel' e1) (simplify_fuel fuel' e2)
        | Sub e1 e2 => Sub (simplify_fuel fuel' e1) (simplify_fuel fuel' e2)
        | Mul e1 e2 => Mul (simplify_fuel fuel' e1) (simplify_fuel fuel' e2)
        | Div e1 e2 => Div (simplify_fuel fuel' e1) (simplify_fuel fuel' e2)
        | Pow e1 n => Pow (simplify_fuel fuel' e1) n
        | Ln e1 => Ln (simplify_fuel fuel' e1)
        | Exp e1 => Exp (simplify_fuel fuel' e1)
        | _ => e
        end
      in e'
  end.

Definition simplify (e : expr) : expr :=
  simplify_fuel 100 e.

(** Differentiate and simplify *)
Definition diff_simplify (e : expr) : expr :=
  simplify (diff e).

(** Count nodes in expression tree *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Const _ => 1
  | Var => 1
  | Add e1 e2 => 1 + expr_size e1 + expr_size e2
  | Sub e1 e2 => 1 + expr_size e1 + expr_size e2
  | Mul e1 e2 => 1 + expr_size e1 + expr_size e2
  | Div e1 e2 => 1 + expr_size e1 + expr_size e2
  | Pow e1 _ => 1 + expr_size e1
  | Ln e1 => 1 + expr_size e1
  | Exp e1 => 1 + expr_size e1
  end.

(** Build nested expression for benchmark *)
Fixpoint nested_poly (n : nat) : expr :=
  match n with
  | O => Var
  | S n' => Add (Mul (Const (Z.of_nat n)) (Pow Var (Z.of_nat n))) (nested_poly n')
  end.

(** Test: differentiate x^2 + 2x + 1 *)
Definition test_expr : expr := Add (Add (Pow Var 2) (Mul (Const 2) Var)) (Const 1).
Definition test_diff : expr := diff_simplify test_expr.

(** Benchmark: differentiate a polynomial of degree n, return size *)
Definition symbolic_diff_bench (n : nat) : nat :=
  let poly := nested_poly n in
  let deriv := diff_simplify poly in
  expr_size deriv.
