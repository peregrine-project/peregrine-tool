(* Pidigits Benchmark
   From the Computer Language Benchmarks Game
   Streaming arbitrary-precision arithmetic
   Uses the unbounded spigot algorithm with Zarith for arbitrary precision *)

(* Linear fractional transformation *)
type lft = { q: Z.t; r: Z.t; s: Z.t; t_: Z.t }

let compose a b =
  { q = Z.(add (mul a.q b.q) (mul a.r b.s));
    r = Z.(add (mul a.q b.r) (mul a.r b.t_));
    s = Z.(add (mul a.s b.q) (mul a.t_ b.s));
    t_ = Z.(add (mul a.s b.r) (mul a.t_ b.t_)) }

let extract lft x =
  Z.(div (add (mul lft.q x) lft.r) (add (mul lft.s x) lft.t_))

let init_lft = { q = Z.one; r = Z.zero; s = Z.zero; t_ = Z.one }

let lftn k =
  let k' = Z.of_int k in
  { q = k';
    r = Z.(add (mul (of_int 4) k') (of_int 2));
    s = Z.zero;
    t_ = Z.(add (mul (of_int 2) k') one) }

let safe lft n =
  Z.equal n (extract lft (Z.of_int 4))

let prod lft n =
  compose { q = Z.of_int 10; r = Z.(mul (of_int (-10)) n); s = Z.zero; t_ = Z.one } lft

let rec pidigits_loop z k (remaining : int) acc =
  if remaining = 0 then acc
  else
    let y = extract z (Z.of_int 3) in
    if safe z y then
      pidigits_loop (prod z y) k (remaining - 1)
        Z.(add (mul acc (of_int 10)) y)
    else
      let z' = compose z (lftn k) in
      pidigits_loop z' (k + 1) remaining acc

let pidigits_number n =
  pidigits_loop init_lft 1 n Z.zero

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 27 in
  let start = Unix.gettimeofday () in
  let result = pidigits_number n in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "Result: %s\n" (Z.to_string result);
  Printf.printf "Time: %.2f ms\n" elapsed
