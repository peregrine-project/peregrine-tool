# Peregrine Command Line Interface
`peregrine --help` for detailed instructions


## `compile` command
```
peregrine compile [OPTION]… PROGRAM_FILE CONFIG_FILE
```

Compile lambda box program using the configuration declared in `CONFIG_FILE` the configuration includes the target backend.

## Backend commands
Commands for the specific backends, configuration file is optional for all of them, if a configuration exists then it is preferred to use the `compile` command instead.

```
peregrine BACKEND FILE [-o FILE]
```

Valid values for `BACKEND` are:
* `wasm`
* `c`
* `ocaml`
* `cakeml`
* `rust`, `rust-gmp`, `rust-i64`, `rust-mixed`, `rust-mixed-narrow`: Rust with different representations of `nat`, `positive`, `N` and `Z`; see [backends.md](backends.md#numeric-representations)
* `elm`
* `lean`
* `fsharp`
* `ast`
* `eval`

The Rust commands, `elm` and `ast typed` work on typed lambda box. Given untyped input they infer the type annotations first (the same inference for all of them), and fail with an error naming the offending constant when the program cannot be typed; see [backends.md](backends.md#rust).

The backend commands other than `ast` take these flags, which select optional middle-end passes. Each takes `true` or `false`; when absent, the backend's default applies (see [middleend.md](middleend.md)).

* `--betared`, `--unboxing`, `--dearg-ctors`, `--dearg-consts`
* `--specialize-instances`: specialize functions at call sites that pass a statically known dictionary (record) value
* `--cse`: hoist repeated closed subterms into a `let`

`--specialize-instances` and `--cse` are off by default and act only on untyped targets (`wasm`, `c`, `ocaml`, `cakeml`, `lean`, `eval`); the typed pipeline of the Rust and Elm commands does not run them. Their correctness rests on axioms ([middleend.md](middleend.md#optional-passes)).

## `validate` command
```
peregrine validate [--config=PATH] [OPTION]… FILE
```

Runs program and optional configuration file validation.



## Common options
These options are common to all commands.

* `--attributes=PATH[,…]`
  Attribute config files, a list of files containing attribute configuration

* `-o VAL, --outfile=VAL`
  Output file

* `-d, --debug`
  Enable debug information

* `-q, --quiet`
  Suppress informational output

* `-v, --verbose`
  Give verbose output
