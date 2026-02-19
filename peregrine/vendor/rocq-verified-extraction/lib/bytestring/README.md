You can use the functions from `caml_bytestring.ml` to convert between `bytestring` extracted from Rocq and OCaml's `string`.
If you do so from `main.ml`, compile into an executable `run` using:

`ocamlopt -o run byte.ml caml_byte.ml caml_bytestring.ml main.ml`
