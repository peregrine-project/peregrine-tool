(* Symbolic Differentiation Benchmark
   Differentiate algebraic expressions symbolically *)

type expr =
  | Const of int
  | Var
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Pow of expr * int
  | Ln of expr
  | Exp of expr

let rec diff = function
  | Const _ -> Const 0
  | Var -> Const 1
  | Add (e1, e2) -> Add (diff e1, diff e2)
  | Sub (e1, e2) -> Sub (diff e1, diff e2)
  | Mul (e1, e2) -> Add (Mul (diff e1, e2), Mul (e1, diff e2))
  | Div (e1, e2) -> Div (Sub (Mul (diff e1, e2), Mul (e1, diff e2)), Mul (e2, e2))
  | Pow (e, n) -> Mul (Mul (Const n, Pow (e, n - 1)), diff e)
  | Ln e -> Div (diff e, e)
  | Exp e -> Mul (Exp e, diff e)

let rec simplify = function
  | Add (Const 0, e2) -> simplify e2
  | Add (e1, Const 0) -> simplify e1
  | Add (Const a, Const b) -> Const (a + b)
  | Sub (e1, Const 0) -> simplify e1
  | Sub (Const a, Const b) -> Const (a - b)
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, e2) -> simplify e2
  | Mul (e1, Const 1) -> simplify e1
  | Mul (Const a, Const b) -> Const (a * b)
  | Div (e1, Const 1) -> simplify e1
  | Pow (_, 0) -> Const 1
  | Pow (e, 1) -> simplify e
  | Add (e1, e2) -> Add (simplify e1, simplify e2)
  | Sub (e1, e2) -> Sub (simplify e1, simplify e2)
  | Mul (e1, e2) -> Mul (simplify e1, simplify e2)
  | Div (e1, e2) -> Div (simplify e1, simplify e2)
  | Pow (e1, n) -> Pow (simplify e1, n)
  | Ln e1 -> Ln (simplify e1)
  | Exp e1 -> Exp (simplify e1)
  | e -> e

let diff_simplify e = simplify (diff e)

let rec expr_size = function
  | Const _ -> 1
  | Var -> 1
  | Add (e1, e2) -> 1 + expr_size e1 + expr_size e2
  | Sub (e1, e2) -> 1 + expr_size e1 + expr_size e2
  | Mul (e1, e2) -> 1 + expr_size e1 + expr_size e2
  | Div (e1, e2) -> 1 + expr_size e1 + expr_size e2
  | Pow (e1, _) -> 1 + expr_size e1
  | Ln e1 -> 1 + expr_size e1
  | Exp e1 -> 1 + expr_size e1

let rec nested_poly = function
  | 0 -> Var
  | n -> Add (Mul (Const n, Pow (Var, n)), nested_poly (n - 1))

let symbolic_diff_bench n =
  let poly = nested_poly n in
  let deriv = diff_simplify poly in
  expr_size deriv

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 20 in
  let start = Unix.gettimeofday () in
  let result = symbolic_diff_bench n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
