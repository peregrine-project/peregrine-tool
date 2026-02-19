(* Quicksort Benchmark
   Functional quicksort using list partitioning *)

let rec partition pivot = function
  | [] -> ([], [])
  | x :: xs ->
    let (lo, hi) = partition pivot xs in
    if x < pivot then (x :: lo, hi) else (lo, x :: hi)

let rec quicksort = function
  | [] -> []
  | [x] -> [x]
  | pivot :: rest ->
    let (lo, hi) = partition pivot rest in
    quicksort lo @ [pivot] @ quicksort hi

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

let quicksort_bench n =
  let l = make_list n in
  let sorted = quicksort l in
  if is_sorted sorted then List.length sorted else 0

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1000 in
  let start = Unix.gettimeofday () in
  let result = quicksort_bench n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
