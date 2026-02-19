open Metarocq_template_plugin

let print_string str = 
  Stdlib.print_string (Caml_bytestring.caml_string_of_bytestring str)

let print_endline str =
  Stdlib.print_endline (Caml_bytestring.caml_string_of_bytestring str)

let print_newline () =
  Stdlib.print_newline ()