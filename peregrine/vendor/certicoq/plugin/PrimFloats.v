From CertiCoq.Plugin Require Import Loader.
From Stdlib Require Import PrimFloat.

CertiCoq Register [
  Stdlib.Floats.PrimFloat.float => "erased",
  Stdlib.Floats.PrimFloat.compare => "prim_float_compare",
  Stdlib.Floats.PrimFloat.eqb => "prim_float_eqb",
  Stdlib.Floats.PrimFloat.ltb => "prim_float_ltb",
  Stdlib.Floats.PrimFloat.leb => "prim_float_leb",
  Stdlib.Floats.PrimFloat.frshiftexp => "prim_float_frshiftexp" with tinfo,
  Stdlib.Floats.PrimFloat.ldshiftexp => "prim_float_ldshiftexp" with tinfo,
  Stdlib.Floats.PrimFloat.normfr_mantissa => "prim_float_normfr_mantissa",
  Stdlib.Floats.PrimFloat.classify => "prim_float_classify",
  Stdlib.Floats.PrimFloat.abs => "prim_float_abs" with tinfo,
  Stdlib.Floats.PrimFloat.sqrt => "prim_float_sqrt" with tinfo,
  Stdlib.Floats.PrimFloat.opp => "prim_float_opp" with tinfo,
  Stdlib.Floats.PrimFloat.div => "prim_float_div" with tinfo,
  Stdlib.Floats.PrimFloat.mul => "prim_float_mul" with tinfo,
  Stdlib.Floats.PrimFloat.add => "prim_float_add" with tinfo,
  Stdlib.Floats.PrimFloat.sub => "prim_float_sub" with tinfo,
  Stdlib.Floats.PrimFloat.of_uint63 => "prim_float_of_uint63" with tinfo,
  Stdlib.Floats.PrimFloat.next_up => "prim_float_next_up" with tinfo,
  Stdlib.Floats.PrimFloat.next_down => "prim_float_next_down" with tinfo ]
Include [ Library "prim_floats.h"  ].
