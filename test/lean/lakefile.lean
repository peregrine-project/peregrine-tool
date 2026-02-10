import Lake
open Lake DSL

package lean_peregrine where
  moreLeanArgs := #["-DautoImplicit=false"]

require lean_to_lambdabox from git
  "https://github.com/4ever2/lean-to-lambdabox" @ "ast-format"

@[default_target]
lean_lib Tests where
  roots := #[`src.Demo, `src.Map]
