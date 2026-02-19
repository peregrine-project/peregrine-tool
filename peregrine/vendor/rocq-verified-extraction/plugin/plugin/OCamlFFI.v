Require Import MetaRocq.Utils.bytestring.
From Malfunction.Plugin Require Import Loader.
From Malfunction.Plugin Require Import PrimInt63.

Axiom (print_int : PrimInt63.int -> unit).
Axiom (print_float : Corelib.Floats.PrimFloat.float -> unit).
Axiom (print_string : string -> unit).
Axiom (print_newline : unit -> unit).
Axiom (print_endline : string -> unit).

Verified Extract Constants [ 
  print_int => "Stdlib.print_int",
  print_float => "Stdlib.print_float",
  print_string => "Rocq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_string",
  print_newline => "Rocq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_newline",
  print_endline => "Rocq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_endline" ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].