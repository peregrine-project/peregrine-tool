type nat = 
  | O
  | S of nat

let plus : nat -> nat -> nat =
  Obj.magic Plus.coq_Init_Nat_add  

let res = plus O (S O)

let rec show_nat n =
  match n with
  | O -> "0"
  | S n -> "(S " ^ show_nat n ^ ")"

let main = Printf.printf "result: %s" (show_nat res)