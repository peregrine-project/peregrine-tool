From Peregrine.Plugin Require Import Loader.
From Peregrine.Tests Require Demo.
From Peregrine.Tests Require Hello.
From Peregrine.Tests Require Map.
From Peregrine.Tests Require Mutual.
From Peregrine.Tests Require Nat.
From Peregrine.Tests Require OddEven.

(* Demo.v *)
Peregrine Extract "extraction/Demo.ast" Demo.test.
Peregrine Extract Typed "extraction/Demo_typed.ast" Demo.test.

(* Hello.v *)
Peregrine Extract "extraction/Hello.ast" Hello.hello.
Peregrine Extract Typed "extraction/Hello_typed.ast" Hello.hello.

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
