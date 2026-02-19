type three = ZERO | ONE | TWO | THREE

let res : three =
  Obj.magic Three.malfunction_Plugin_tests_test_extract_two

let rec show_three n =
  match n with
  | ZERO -> "0"
  | ONE -> "1"
  | TWO -> "2"
  | THREE -> "3"

let main = Printf.printf "result: %s" (show_three res)