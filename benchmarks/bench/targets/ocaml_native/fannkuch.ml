(* Fannkuch Redux Benchmark
   From the Computer Language Benchmarks Game
   Indexed-access to tiny integer-sequence

   Purely functional implementation using immutable lists *)

(* Reverse the first n elements of a list, keeping the rest *)
let rec reverse_prefix_aux n l acc =
  match n, l with
  | 0, rest -> acc @ rest
  | n, x :: xs -> reverse_prefix_aux (n - 1) xs (x :: acc)
  | _, [] -> acc

let reverse_prefix n l = reverse_prefix_aux n l []

(* One flip operation: reverse prefix of length = first element + 1 *)
let flip perm =
  match perm with
  | [] -> []
  | x :: _ -> reverse_prefix (x + 1) perm

(* Count flips until first element is 0 *)
let rec count_flips_aux perm count =
  match perm with
  | [] -> count
  | 0 :: _ -> count
  | _ -> count_flips_aux (flip perm) (count + 1)

let count_flips perm = count_flips_aux perm 0

(* Rotate first n elements: [a; b; c; d; ...] -> [b; c; d; a; ...] *)
let rotate_prefix l n =
  let rec split_at i acc = function
    | [] -> (List.rev acc, [])
    | xs when i = 0 -> (List.rev acc, xs)
    | x :: xs -> split_at (i - 1) (x :: acc) xs
  in
  match l, n with
  | [], _ -> []
  | l, 0 -> l
  | l, 1 -> l
  | x :: xs, n ->
    let (prefix_rest, suffix) = split_at (n - 1) [] xs in
    prefix_rest @ [x] @ suffix

(* Get element at position i in a list *)
let rec get_at l i =
  match l, i with
  | [], _ -> 0
  | x :: _, 0 -> x
  | _ :: xs, n -> get_at xs (n - 1)

(* Set element at position i in a list *)
let rec set_at l i v =
  match l, i with
  | [], _ -> []
  | _ :: xs, 0 -> v :: xs
  | x :: xs, n -> x :: set_at xs (n - 1) v

(* Find the index i where count[i] < i, starting from index 1 *)
let rec find_i counts i n =
  if i >= n then None
  else if get_at counts i < i then Some i
  else find_i counts (i + 1) n

(* Reset counts from 0 to i-1 to 0 *)
let rec reset_counts counts i =
  match counts, i with
  | [], _ -> []
  | c :: cs, 0 -> c :: cs
  | _ :: cs, n -> 0 :: reset_counts cs (n - 1)

(* Generate next permutation using Heap's algorithm variant *)
let next_perm perm counts n =
  match find_i counts 1 n with
  | None -> None
  | Some i ->
    let perm' = rotate_prefix perm (i + 1) in
    let counts' = set_at counts i (get_at counts i + 1) in
    let counts'' = reset_counts counts' i in
    Some (perm', counts'')

(* Main loop: iterate through all permutations tracking max flips *)
let rec fannkuch_loop perm counts n max_flips =
  let flips = count_flips perm in
  let max_flips' = max max_flips flips in
  match next_perm perm counts n with
  | None -> max_flips'
  | Some (perm', counts') -> fannkuch_loop perm' counts' n max_flips'

(* Create initial permutation [0; 1; 2; ...; n-1] *)
let rec range_aux i n acc =
  if i >= n then List.rev acc
  else range_aux (i + 1) n (i :: acc)

let range n = range_aux 0 n []

(* Create list of n zeros *)
let rec replicate n v =
  if n <= 0 then []
  else v :: replicate (n - 1) v

let fannkuch n =
  let perm = range n in
  let counts = replicate n 0 in
  fannkuch_loop perm counts n 0

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 7 in
  let start = Unix.gettimeofday () in
  let result = fannkuch n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %d\n" result;
  Printf.printf "Time: %.2f ms\n" elapsed
