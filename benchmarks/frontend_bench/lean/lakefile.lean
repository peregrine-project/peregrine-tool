import Lake
open Lake DSL

package lean_peregrine where
  moreLeanArgs := #["-DautoImplicit=false"]

require lean_to_lambdabox from
  "../../../lean_frontend"

@[default_target]
lean_lib Benchmarks where
  roots := #[`BinaryTrees, `Fannkuch, `Sieve, `Quicksort, `Arith]
