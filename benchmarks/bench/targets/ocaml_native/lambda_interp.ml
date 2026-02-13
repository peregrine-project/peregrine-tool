(* Lambda Calculus Interpreter Benchmark
   Untyped lambda calculus with de Bruijn indices *)

type term =
  | Var of int
  | Lam of term
  | App of term * term
  | Lit of int
  | Add of term * term
  | Mul of term * term
  | IfZ of term * term * term

type value =
  | VInt of int
  | VClosure of value list * term

let lookup n env =
  if n < List.length env then Some (List.nth env n) else None

let rec eval env = function
  | Var n -> lookup n env
  | Lam body -> Some (VClosure (env, body))
  | App (f, arg) ->
    (match eval env f with
     | Some (VClosure (env', body)) ->
       (match eval env arg with
        | Some v -> eval (v :: env') body
        | None -> None)
     | _ -> None)
  | Lit n -> Some (VInt n)
  | Add (e1, e2) ->
    (match eval env e1, eval env e2 with
     | Some (VInt n1), Some (VInt n2) -> Some (VInt (n1 + n2))
     | _ -> None)
  | Mul (e1, e2) ->
    (match eval env e1, eval env e2 with
     | Some (VInt n1), Some (VInt n2) -> Some (VInt (n1 * n2))
     | _ -> None)
  | IfZ (cond, then_, else_) ->
    (match eval env cond with
     | Some (VInt 0) -> eval env then_
     | Some (VInt _) -> eval env else_
     | _ -> None)

let to_int = function
  | Some (VInt n) -> n
  | _ -> 0

(* Factorial using explicit recursion pattern *)
let rec make_fact_aux = function
  | 0 -> Lit 1
  | n ->
    Lam (IfZ (Var 0,
              Lit 1,
              Mul (Var 0, App (make_fact_aux (n - 1), Add (Var 0, Lit (-1))))))

let factorial_term = make_fact_aux 20

let lambda_interp_bench n =
  to_int (eval [] (App (factorial_term, Lit n)))

(* Church numerals *)
let church_zero = Lam (Lam (Var 0))
let church_succ =
  Lam (Lam (Lam (App (Var 1, App (App (Var 2, Var 1), Var 0)))))

let rec church_num = function
  | 0 -> church_zero
  | n -> App (church_succ, church_num (n - 1))

let church_to_int =
  Lam (App (App (Var 0, Lam (Add (Var 0, Lit 1))), Lit 0))

let church_add =
  Lam (Lam (Lam (Lam (App (App (Var 3, Var 1), App (App (Var 2, Var 1), Var 0))))))

let church_bench n =
  let cn = church_num n in
  let add_nn = App (App (church_add, cn), cn) in
  to_int (eval [] (App (church_to_int, add_nn)))

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 10 in
  let start = Unix.gettimeofday () in
  let result = lambda_interp_bench n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
