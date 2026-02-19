

Definition benchArith (n : nat) : nat :=
  Nat.pow 2 (3 + ((3 * n) - n)).

From Peregrine.Plugin Require Import Loader.

Peregrine Extract "ast/Arith.ast" benchArith.
Peregrine Extract Typed "ast/Arith_typed.ast" benchArith.
