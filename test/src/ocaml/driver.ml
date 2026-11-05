type bool_ = False | True

type 'a list_ =
| Nil
| Cons of 'a * 'a list_

type nat =
| O
| S of nat

type 'a option_ =
| Some of 'a
| None

type ('a, 'b) prod_ =
| Pair of 'a * 'b

let pp_bool = function
| False -> print_string "false"
| True -> print_string "true"

let rec pp_list pp_a = function
| Nil -> print_string "nil"
| Cons (x, xs) ->
  print_string "(cons ";
  pp_a x;
  print_string " ";
  pp_list pp_a xs;
  print_string ")"

let rec pp_nat = function
| O -> print_string "O"
| S n ->
  print_string "(S ";
  pp_nat n;
  print_string ")"

let pp_option pp_a = function
| Some a ->
  print_string "(Some ";
  pp_a a;
  print_string ")"
| None -> print_string "None"

let pp_prod pp_a pp_b = function
| Pair (a, b) ->
  print_string "(pair ";
  pp_a a;
  print_string " ";
  pp_b b;
  print_string ")"
