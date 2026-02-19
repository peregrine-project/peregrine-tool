
(* let coq_Floats_PrimFloat_normfr_mantissa = Float64.normfr_mantissa *)

(* let coq_Floats_PrimFloat_frshiftexp = Float64.frshiftexp *)

(* let coq_Floats_PrimFloat_abs = Float64.abs *)

(* let coq_Floats_PrimFloat_ltb = fun f1 f2 -> not (Float64.lt f1 f2) *)

(* let coq_Floats_PrimFloat_eqb = fun f1 f2 -> not (Float64.eq f1 f2) *)

(* let coq_Floats_PrimFloat_div = Float64.div *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_lsr = Uint63.l_sr *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_lsl = Uint63.l_sl *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_land = Uint63.l_and *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_lor = Uint63.l_or *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_sub = Uint63.sub *)

(* let coq_Numbers_Cyclic_Int63_PrimInt63_eqb f1 f2 = not (Uint63.equal f1 f2) *)

(* let print_kername = fun x -> print_string (Metarocq_template_plugin.Caml_bytestring.caml_string_of_bytestring (snd x)) ; Printf.printf ("\n%!") *)

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

let def_VerifiedExtraction_Benchmarks_lib_vs_HELLO = fun _ x -> 
  (* Printf.printf "Returning in map\n%!" ; print_obj x ; Printf.printf "\n%!" ; *) x

let def_print_arg na x =
()
  (* Printf.printf "Function %s called on %!" na ; print_obj x ; Printf.printf "\n%!" *)
 (* = fun x -> Printf.printf ("%i\n%!") (Obj.tag x) ; Printf.printf ("%b\n%!") (Obj.is_block x) ; if Obj.is_block x then Printf.printf ("Size: %i\n%!") (Obj.size x) else () *)

(* let print_obj = fun x -> Printf.printf ("%i\n%!") (Obj.tag x) ; Printf.printf ("%b\n%!") (Obj.is_block x) ; if Obj.is_block x then Printf.printf ("Size: %i\n%!") (Obj.size x) else () *)

let print_int = fun x -> Printf.printf ("%i\n%!") x

let def_print_string = fun x -> Printf.printf ("Global constant %s\n%!") x

let print_hello = fun (x : unit) -> Printf.printf ("Hello\n%!")

(* let print = fun x -> print_string (Metarocq_template_plugin.Caml_bytestring.caml_string_of_bytestring x) ; Printf.printf ("\n%!") *)
