From Stdlib Require ZArith Vector Streams.StreamMemo.
From Stdlib Require Import String.
From Malfunction Require Import PrintMli.
From VerifiedExtraction Require Import Loader Extraction OCamlFFI.
From MetaRocq.Template Require Import All.

Definition rocq_true := true.

(** By default, the [Verified Extraction] command prints out the extracted malfunction code (to the notices channel). *)
Verified Extraction rocq_true. 

(** The generated code is 
   (module ($def_tutorial_rocq_true 1) ($def_main $def_tutorial_rocq_true) ($rocq_true $def_tutorial_rocq_true) ($main $def_main) (export $rocq_true $main)) *)
(* It can be written down to a file using: *)

Verified Extraction rocq_true "rocq_true.mlf".

(* The default output directory is the working directory of your Rocq process, but it can also be set: *)

Set Verified Extraction Build Directory "_build".

(** The [-fmt] option provides a somewhat clearer output: *)

Verified Extraction -fmt rocq_true "rocq_true.mlf".

(* _build/rocq_true.mlf: 

(module ($def_tutorial_rocq_true 1) ($def_main $def_tutorial_rocq_true)
  ($rocq_true $def_tutorial_rocq_true) ($main $def_main)
  (export $rocq_true $main)) *)

(* [.mlf] files can be compiled using the [malfunction] program, which is a thin wrapper
  around [ocamlopt]. The [.mlf] files needs to be accompanied by a [.mli] file giving the
  expected OCaml types of the exported definitions.
  A MetaRocq metaprogram defined in the [Malfunction.PrintMli] library imported above
  provides a default interface: *)

MetaRocq Run Print mli rocq_true.
(* In Rocq's info channel: 
    
  val rocq_true : bool *)

(** Copying this declaration in `rocq_true.mli`, one can then compile the files as follow:

    # ocamlc rocq_true.mli
    (* produces a .cmi file to be read by malfunction *)
    # malfunction rocq_true.mlf
    (* produces rocq_true.cmx which exposes the `rocq_true` definition *)
*)

(** In general, [Print Mli] can produce interfaces that contain types that are marked as unsupported 
    in OCaml and replaced by `Obj.t`. We advise to not export such type definitions which can break 
    interoperability but keep in the `.mli` interface only firstorder types, for which the correctness
    guarantess of the extraction hold. *)

(** Besides producing standalone `.mlf` files, the plugin is also capable of compiling and running the 
  extracted programs itself. To do so, it relies on an `opam` installation to be available in the running 
  environment of the Rocq process, which should include the `malfunction` package. *)

Set Verified Extraction Opam Path "/usr/local/bin/opam".

(** For quick testing of extracted code, one can build the code as a plugin, which can be dynamically loaded 
    with Rocq and run directly. The value of the program should be firstorder so that it can be read back as a 
    Rocq value. This is the case of booleans. *)  

Verified Extraction -compile-plugin -run rocq_true "rocq_true.mlf".
(* = true *)

(** The plugin has a few diagnostics and customization flags:
   The `-verbose` flag produces debug output (useful for tracking compilation issues),  
   The `-time` flag reports the compilation and running times of the command.
   The `-optimize` flag uses OCaml's -O2 option to compile the malfunction code.  *)
Verified Extraction -time -verbose -optimize -compile-plugin -run rocq_true "rocq_true.mlf".

(** The Rocq programs can make use of axioms that are realised by ocaml libraries and linked to the resulting program.
    By default, there is an `FFI` library allowing to access Rocq's info, notice and debug channels as well as raising 
    Rocq errors (coq_user_error) that is realized by linking back with Rocq's code, as described in the RocqMsgFFI library. *)
From Malfunction Require Import FFI. 
From VerifiedExtraction Require Import RocqMsgFFI.

(** The following definition prints out the string representation of true (`show` is a typeclass method for serializing to a string) *)
Definition msg_true := coq_msg_info (show true).

(** Running the plugin produces as side effect a call to [coq_msg_info], printing to the [info] pannel of your IDE. *)
Verified Extraction -compile-plugin -run msg_true "rocq_true.mlf".
(* = tt 
 
  In Rocq's Info channel:

  true

*)

(** The FFI support is used to bind primitive type operations to implementations in OCaml as well. For example 
    one can compute with primitive integers. *)

From Stdlib Require Import PrimInt63 Sint63.
Definition test_primint := 
  let _ := coq_msg_info ("Min int is " ++ show (wrap_int Sint63.min_int)) in (* Otherwise is interpreted as unsigned *)
  let _ := coq_msg_info ("Max int is " ++ show (wrap_int Sint63.max_int)) in
  tt.

(** We disable this warning of MetaRocq as all primitive axioms are properly bound to OCaml code during compilation *)  
Set Warnings "-primitive-turned-into-axiom".

Verified Extraction -fmt -compile-plugin -run test_primint "test_primint.mlf".

(* Info channel: 

   Min int is -4611686018427387904
   Max int is 4611686018427387903 *)

Eval compute in Sint63.min_int.
(* = (-4611686018427387904)%sint63
    : int *)

(* Coinductive types are also supported. They are compiled down to fixpoints + lazy/force, so they can be 
  used to implement e.g. efficient memoization.  *) 
Module CoInd.
Set Primitive Projections.
CoInductive stream := Cons { head : nat; tail : stream }.

Fixpoint take (n : nat) (s : stream) : list nat :=
  match n with
  | 0 => []
  | S n => s.(head) :: take n s.(tail)
  end.
  
CoFixpoint ones : stream := {| head := 1; tail := ones |}.
Definition test_ones := print_string (show (take 10 ones)).

(** Here instead of building a plugin, we build a standalone ocaml program using `-compile-with-coq` 
    and rely on a small OCaml FFI for printing strings/integers or floats defined in the `OCamlFFI` library.
    The `-run` flag runs the program and relays the stdout and stderr channels of the standalone process to 
    Rocq's notices channels. *)

Verified Extraction -fmt -unsafe -compile-with-coq -run test_ones "ones.mlf".

(* Notices channel: 
  [1,1,1,1,1,1,1,1,1,1]
  *)
End CoInd.

(** Verified extraction has a -typed variant which uses type information to be able to remove unused arguments of
    constants and constructors. With this option we can unbox existential types for example, which the 
    standard verified extraction would just keep around an extra erased argument for the constructor
    (identifiable as `(let (rec ($reccall ...))))` below, which is the implementation of erased values in malfunction) *)

Definition sub : { x : nat | x = 0 } := @exist _ _ 0 eq_refl.
Verified Extraction sub.
(* (module ($def_tutorial_sub (block (tag 0) 0 (let (rec ($reccall (lambda ($wildcard0) $reccall))) $reccall))) ($def_main $def_tutorial_sub) ($sub $def_tutorial_sub) ($main $def_main) (export $sub $main)) *)

Verified Extraction -typed sub.

(* (module ($def_tutorial_sub (block (tag 0) 0)) ($def_main $def_tutorial_sub) ($sub $def_tutorial_sub) ($main $def_main) (export $sub $main)) *)
(** Here the typed extraction completely removes the use of the `exist` constructor, and the `eq_refl` proof argument hence disappears.
    Beware that the `Print mli` metaprogram does not (yet) expect `-typed` to be used and might produce an interface that is incorrect for an implementation
    extracted with `-typed`. One should remove erasable types entirely and unbox constructors accordingly in the interface. *)

(** This closes the tutorial. See the README.md file for more information about the `Verified Extraction` commands and optional flags. *)
