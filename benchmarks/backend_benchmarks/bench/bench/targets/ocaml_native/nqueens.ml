(* N-Queens Benchmark
   Classic backtracking: place N queens on NxN board with no attacks *)

let attacks c r c' =
  let diff = abs (c' - c) in
  c = c' || diff = r

let rec safe_aux placed r c =
  match placed with
  | [] -> true
  | c' :: rest ->
    if attacks c r c' then false
    else safe_aux rest (r - 1) c

let safe placed c = safe_aux placed (List.length placed) c

let range n =
  let rec aux i acc =
    if i < 0 then acc else aux (i - 1) (i :: acc)
  in aux (n - 1) []

let rec solve_aux n row placed =
  if row = n then
    [placed]
  else
    let candidates = List.filter (fun c -> safe placed c) (range n) in
    List.concat_map (fun c -> solve_aux n (row + 1) (placed @ [c])) candidates

let solve n = solve_aux n 0 []

let nqueens n = List.length (solve n)

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 8 in
  let start = Unix.gettimeofday () in
  let result = nqueens n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
