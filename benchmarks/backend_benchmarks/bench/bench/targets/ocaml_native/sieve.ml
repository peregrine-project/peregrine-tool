(* Sieve of Eratosthenes Benchmark
   Find all prime numbers up to a given limit *)

let range_from start limit =
  let rec aux i acc =
    if i < start then acc else aux (i - 1) (i :: acc)
  in aux limit []

let remove_multiples p l =
  List.filter (fun n -> n mod p <> 0 || n = p) l

let rec sieve_aux candidates primes =
  match candidates with
  | [] -> primes
  | p :: rest -> sieve_aux (remove_multiples p rest) (primes @ [p])

let sieve n =
  if n < 2 then []
  else sieve_aux (range_from 2 n) []

let count_primes n = List.length (sieve n)

let sum_primes n = List.fold_left ( + ) 0 (sieve n)

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 10000 in
  let start = Unix.gettimeofday () in
  let result = count_primes n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
