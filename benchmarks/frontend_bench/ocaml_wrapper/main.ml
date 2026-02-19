open Printf
open Types


let main =
  let n = to_nat @@ int_of_string @@ Sys.argv.(1) in
  let x = {{NAME}}.main n in
  print_endline @@ string_of_int @@ of_nat x
