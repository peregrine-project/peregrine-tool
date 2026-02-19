(* Binary Trees Benchmark
   From the Computer Language Benchmarks Game
   Allocate and deallocate many binary trees *)

type tree =
  | Leaf
  | Node of tree * int * tree

let rec make depth =
  match depth with
  | 0 -> Leaf
  | n -> Node (make (n - 1), 0, make (n - 1))

let rec check = function
  | Leaf -> 0
  | Node (l, _, r) -> 1 + check l + check r

let make_check depth = check (make depth)

let stretch_tree max_depth = make_check (max_depth + 1)

let calc_iterations max_depth depth min_depth =
  1 lsl (max_depth - depth + min_depth)

let rec run_iterations iterations depth acc =
  match iterations with
  | 0 -> acc
  | n -> run_iterations (n - 1) depth (acc + make_check depth)

let rec run_depths_aux min_depth current_depth max_depth acc =
  if current_depth > max_depth then acc
  else
    let iterations = calc_iterations max_depth current_depth min_depth in
    let result = run_iterations iterations current_depth 0 in
    run_depths_aux min_depth (current_depth + 2) max_depth (acc @ [result])

let run_depths min_depth max_depth =
  run_depths_aux min_depth min_depth max_depth []

let binary_trees_main n =
  let min_depth = 4 in
  let max_depth = max (min_depth + 2) n in
  let stretch = stretch_tree max_depth in
  let long_tree = make max_depth in
  let depth_results = run_depths min_depth max_depth in
  let long_check = check long_tree in
  (stretch, depth_results, long_check)

let binary_trees_simple n =
  let (stretch, _, long_check) = binary_trees_main n in
  stretch + long_check

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 10 in
  let start = Unix.gettimeofday () in
  let result = binary_trees_simple n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
