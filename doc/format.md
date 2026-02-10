# Peregrine input format

The peregrine middle end takes two input files 1) a $\lambda_\square$ program formatted as S-expressions 2) pipeline configuration formatted as S-expressions. Parsers and printers for both are found in [theories/serialization/](/theories/serialization/).

The S-expression format supports string and integer literals. Both files should be UTF-8 encoded. Non-ascii characters are only supported in S-expression string literals, and the following escape sequences are supported: \n, \r, \t, \\\, \\"

Rocq lists and pairs are translated to S-epxression lists. Records are translated to a list starting with an atom corresponding to the record name using the same capitalization as the Rocq type, followed by each field element in the order that they are defined in source. Field names are not included in the S-expressions.
E.g.
```coq
Record foo := { bar : nat; baz : string; }.
Definition s : foo := {| bar := 0; baz := "hello"; |}.
(* In S-expression form: *)
(* (foo 0 "hello") *)
```
Inductives are similarly translated. For an n-ary constructor it is translated to a list of length n+1 with the first element being an atom corresponding to the constructor name followed by the constructor arguments. Nullary constructors are translated to a single atom corresponding to the constructor name.
```coq
Inductive foo :=
| bar : foo
| baz : nat -> foo -> foo.
Definition s : foo := baz 1 (baz 2 bar).
(* In S-expression form: *)
(* (baz 0 (baz 2 bar)) *)
```

## Lambda Box AST
LambdaBox has two variants 1) untyped lambda box ($\lambda_\square$) 2) typed lambda box ($\lambda_\square^T$).
The main type denoting a LambdaBox AST is `PAst`

[`PAst` definition](/theories/PAst.v)
```coq
Definition typed_env := ExAst.global_env.
Definition untyped_env := EAst.global_context.

Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed : typed_env -> option EAst.term -> PAst.
```
Both ASTs consist of an environment of constant- and inductive-declarations, and an optional term representing the main function of the program.

```
(Untyped (...) (Some ...))
(Typed (...) None)
```


### Untyped $\lambda_\square$ AST

### Typed $\lambda_\square^T$ AST

## Configuration

### General configuration

### Backend configuration
