(* Treesort Benchmark
   Sorting by inserting into BST then flattening with in-order traversal *)

type bst = Leaf | Node of bst * int * bst

let rec insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, v, r) ->
    if x < v then Node (insert x l, v, r)
    else if x > v then Node (l, v, insert x r)
    else Node (l, v, r)  (* duplicate *)

let build_tree l =
  List.fold_left (fun t x -> insert x t) Leaf l

let rec inorder = function
  | Leaf -> []
  | Node (l, v, r) -> inorder l @ [v] @ inorder r

let treesort l = inorder (build_tree l)

let make_list n =
  let rec aux seed n acc =
    if n = 0 then acc
    else
      let next = (seed * 1103515245 + 12345) mod 2147483648 in
      aux next (n - 1) (next :: acc)
  in aux 42 n []

let rec is_sorted = function
  | [] -> true
  | [_] -> true
  | x :: (y :: _ as rest) -> x <= y && is_sorted rest

let treesort_bench n =
  let l = make_list n in
  let sorted = treesort l in
  if is_sorted sorted then List.length sorted else 0

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1000 in
  let start = Unix.gettimeofday () in
  let result = treesort_bench n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
