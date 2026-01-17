From MetaRocq.Erasure Require EAst.
From Peregrine Require LambdaBoxToWasm.
From Peregrine Require LambdaBoxToRust.
From Peregrine Require LambdaBoxToElm.
From Peregrine Require LambdaBoxToC.
Local Unset Universe Checking. (* TODO: fix universe inconsistency *)
From Peregrine Require LambdaBoxToOCaml.
Local Set Universe Checking.


Definition l_box_to_wasm :=
    LambdaBoxToWasm.run_translation.

Definition l_box_to_rust :=
    LambdaBoxToRust.box_to_rust.

Definition l_box_to_elm :=
    LambdaBoxToElm.box_to_elm.

Definition l_box_to_c :=
    LambdaBoxToC.run_translation.

Definition l_box_to_ocaml :=
    LambdaBoxToOCaml.box_to_ocaml.
