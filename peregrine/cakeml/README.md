# CakeML backend for Peregrine

## Meta

- Author(s):
  - Anon
- Maintainer:
  - Anon
- License: [MIT License](LICENSE)
- Compatible Rocq versions: 9.0

## CakeML-related files

The files in `theories/CakeML` are arranged to mirror the structure of  [CakeML](https://github.com/CakeML/cakeml/tree/e1650fc504837c0fbd3931cc5066914ffdc9d877).
- [ast.v](/Exceptions/ast.v ) : the basic defintions
- [functions.v](Exceptions/functions.v) : some generic functions and relations.
- [namespace.v](Exceptions/namespace.v) : the definitoons and funcions to manipulate namespace
- [semanticPrimitives.v](Exceptions/semanticPrimitives.v) : all the other helpers functions
- [smallstep.v](Exceptions/smallstep.v) : a functionnal small-step semantic for CakeML
- [smallstep_rel.v]( Exceptions/smallstep_rel.v) : a relationnal small-step semantic for CakeML
- [bigstep.v](Exceptions/bigstep.v) : a relationnal big-step semantic for CakeML
- [Proofs](Exceptions/proofs) : The equivalence proofs

## Backend

The other files in `theories` are similar to `rocq-verified-extraction`:

- `FFI.v` is an administrative file
- `Compile.v` has the compilation function
- `Pipeline.v` has the MetaRocq pipeline instantiated
- `Serialize.v` has a printer to s-expressions
