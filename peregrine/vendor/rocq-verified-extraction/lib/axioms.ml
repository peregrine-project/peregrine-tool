
let rec print_obj x = 
  let x = Obj.magic x in
  if Obj.is_block x then let size = Obj.size x in
                           if Obj.tag x = 247 then
                              Printf.printf "POINTER%!"
                           else
                           (Printf.printf ("(block[%i] (tag %i) %!") (Obj.size x) (Obj.tag x) ;
                           for i = 0 to size - 1 do
                             print_obj (Obj.field x i)
                           done;
                           Printf.printf ")")
  else  Printf.printf ("%i %!") x

let def_print_arg na x = 
  Printf.printf "Function %s called %!" na ; print_obj x ; Printf.printf "\n%!"

let def_print_string = fun x -> Printf.printf ("Global constant %s\n%!") x

let print_hello = fun (x : unit) -> Printf.printf ("Hello\n%!")
