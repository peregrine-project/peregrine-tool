(* The primitives of FreeIO.v for the OCaml backend.  Peregrine refers to an
   axiom [K] as [Axioms.def_K]; the world is the constant constructor [token],
   and a pair is a two-field block, as an OCaml tuple. *)
let def_FreeIO_put_int = fun (n : int) (w : Obj.t) -> print_endline (string_of_int n); w
let def_FreeIO_get_int = fun (w : Obj.t) -> (int_of_string (String.trim (input_line stdin)), w)
(* Rocq's primitive integer addition, quoted as an axiom: 63-bit wrapping. *)
let def_Corelib_Numbers_Cyclic_Int63_PrimInt63_add = fun (a : int) (b : int) -> a + b
