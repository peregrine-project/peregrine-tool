From Stdlib Require Import List.

Import ListNotations.

Definition String : Type := list nat.

Definition hello : String :=
  [72; 101; 108; 108; 111; 33].
