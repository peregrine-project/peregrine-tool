(* Tak (Takeuchi) Function Benchmark
   tak(x, y, z) = if x <= y then z
                  else tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y)) *)

let rec tak x y z =
  if x <= y then z
  else tak (tak (x - 1) y z) (tak (y - 1) z x) (tak (z - 1) x y)

let () =
  let x = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 18 in
  let y = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 12 in
  let z = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 6 in
  let start = Unix.gettimeofday () in
  let result = tak x y z in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
