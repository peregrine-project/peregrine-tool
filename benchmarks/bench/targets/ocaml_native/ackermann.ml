(* Ackermann Function Benchmark
   A(0, n) = n + 1
   A(m, 0) = A(m-1, 1)
   A(m, n) = A(m-1, A(m, n-1)) *)

let rec ackermann m n =
  match m with
  | 0 -> n + 1
  | _ ->
    match n with
    | 0 -> ackermann (m - 1) 1
    | _ -> ackermann (m - 1) (ackermann m (n - 1))

let () =
  let m = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 3 in
  let n = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 10 in
  let start = Unix.gettimeofday () in
  let result = ackermann m n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
