import Lake
open Lake DSL

package lean_peregrine where
  moreLeanArgs := #["-DautoImplicit=false"]

require lean_to_lambdabox from path
  "../../../lean_frontend"

@[default_target]
lean_lib Tests where
  roots := #[`src.Demo, `src.Map]
