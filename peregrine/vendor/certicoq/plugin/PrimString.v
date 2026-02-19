From CertiCoq.Plugin Require Import Loader.
From Stdlib Require Import PString.

CertiCoq Register [
    Stdlib.Strings.PrimString.compare => "prim_string_compare",
      Stdlib.Strings.PrimString.get => "prim_string_get",
      Stdlib.Strings.PrimString.length => "prim_string_length"
  ]
  Include [ Library "prim_string.h" ].
