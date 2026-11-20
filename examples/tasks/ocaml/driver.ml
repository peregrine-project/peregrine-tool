let rec nat (x : Obj.t) acc = if Obj.is_int x then acc else nat (Obj.field x 0) (acc + 1)
let () = print_endline (string_of_int (nat (Obj.repr Tasks.main) 0))
