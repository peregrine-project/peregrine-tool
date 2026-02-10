import Lake
open Lake DSL

package lean_peregrine where
  moreLeanArgs := #["-DautoImplicit=false"]

require lean_to_lambdabox from git
  "https://github.com/peregrine-project/lean-to-lambdabox" @ "main"

@[default_target]
lean_lib Tests where
  roots := #[`src.Demo, `src.Map]
