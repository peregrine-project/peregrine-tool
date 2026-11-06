From Peregrine.Plugin Require Import Loader.
From Peregrine.Tests Require Classy.
From Peregrine.Tests Require Closure.
From Peregrine.Tests Require CoStream.
From Peregrine.Tests Require Prims.
From Peregrine.Tests Require PrimInt.
From Peregrine.Tests Require Demo.
From Peregrine.Tests Require Hello.
From Peregrine.Tests Require EtaFix.
From Peregrine.Tests Require Id.
From Peregrine.Tests Require Map.
From Peregrine.Tests Require Mutual.
From Peregrine.Tests Require Nat.
From Peregrine.Tests Require OddEven.
From Peregrine.Tests Require OpenCase.
From Peregrine.Tests Require Params.
From Peregrine.Tests Require Phantom.
From Peregrine.Tests Require Remap.
From Peregrine.Tests Require PolyLet.

(* Classy.v *)
Peregrine Extract "extraction/Classy.ast" Classy.test.
Peregrine Extract Typed "extraction/Classy_typed.ast" Classy.test.

(* Closure.v *)
Peregrine Extract "extraction/Closure.ast" Closure.test.
Peregrine Extract Typed "extraction/Closure_typed.ast" Closure.test.

(* CoStream.v *)
Peregrine Extract "extraction/CoStream.ast" CoStream.test.
Peregrine Extract Typed "extraction/CoStream_typed.ast" CoStream.test.

(* Prims.v *)
Peregrine Extract "extraction/Prims.ast" Prims.test.
Peregrine Extract Typed "extraction/Prims_typed.ast" Prims.test.

(* PrimInt.v *)
Peregrine Extract "extraction/PrimInt.ast" PrimInt.test.
Peregrine Extract Typed "extraction/PrimInt_typed.ast" PrimInt.test.

(* Demo.v *)
Peregrine Extract "extraction/Demo.ast" Demo.test.
Peregrine Extract Typed "extraction/Demo_typed.ast" Demo.test.

(* Hello.v *)
Peregrine Extract "extraction/Hello.ast" Hello.hello.
Peregrine Extract Typed "extraction/Hello_typed.ast" Hello.hello.

(* EtaFix.v *)
Peregrine Extract "extraction/EtaFix.ast" EtaFix.test.
Peregrine Extract Typed "extraction/EtaFix_typed.ast" EtaFix.test.

(* Id.v *)
Peregrine Extract "extraction/Id.ast" Id.test.
Peregrine Extract Typed "extraction/Id_typed.ast" Id.test.

(* Map.v *)
Peregrine Extract "extraction/Map.ast" Map.ys.
Peregrine Extract Typed "extraction/Map_typed.ast" Map.ys.

(* Mutual.v *)
Peregrine Extract "extraction/Mutual.ast" Mutual.test.
Peregrine Extract Typed "extraction/Mutual_typed.ast" Mutual.test.

(* Nat.v *)
Peregrine Extract "extraction/Nat.ast" Nat.thing.
Peregrine Extract Typed "extraction/Nat_typed.ast" Nat.thing.

(* OddEven.v *)
Peregrine Extract "extraction/OddEven.ast" OddEven.test.
Peregrine Extract Typed "extraction/OddEven_typed.ast" OddEven.test.

(* OpenCase.v *)
Peregrine Extract "extraction/OpenCase.ast" OpenCase.test.
Peregrine Extract Typed "extraction/OpenCase_typed.ast" OpenCase.test.

(* Params.v *)
Peregrine Extract "extraction/Params.ast" Params.test.
Peregrine Extract Typed "extraction/Params_typed.ast" Params.test.

(* Phantom.v *)
Peregrine Extract "extraction/Phantom.ast" Phantom.test.
Peregrine Extract Typed "extraction/Phantom_typed.ast" Phantom.test.

(* Remap.v *)
Peregrine Extract "extraction/Remap.ast" Remap.test.
Peregrine Extract Typed "extraction/Remap_typed.ast" Remap.test.

(* PolyLet.v *)
Peregrine Extract "extraction/PolyLet.ast" PolyLet.test.
Peregrine Extract Typed "extraction/PolyLet_typed.ast" PolyLet.test.
