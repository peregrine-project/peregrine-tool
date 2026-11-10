export type Timeout = { type: "error", reason: "timeout" };
export type RuntimeError = { type: "error", reason: "runtime error", error: string };
export type CompileError = { type: "error", reason: "compile error", compiler: string, code: number, error: string };
export type IncorrectResult = { type: "error", reason: "incorrect result", expected: string, actual: string };
export type ExecFailure = Timeout | RuntimeError | CompileError | IncorrectResult;
export type ExecSuccess = { type: "success", time: number }
// Result of executing/compiling a test
export type ExecResult = ExecFailure | ExecSuccess;


// Type representing simple types in the test programs
// Used to specify parameter and return types for the main function
export enum SimpleType {
  Nat,
  Bool,
  UInt63
}

// Complex types that have type variables
type ComplexType =
| { type: "list", a_t: ProgramType }
| { type: "option", a_t: ProgramType }
| { type: "prod", a_t: ProgramType, b_t: ProgramType }

// Type representing types in the test programs
// Used to specify parameter and return types for the main function
export type ProgramType = SimpleType | ComplexType;


// Languages support by the lambda box compiler
export enum Lang {
  OCaml = "OCaml",
  C = "C",
  Wasm = "WebAssembly",
  LLVM = "LLVM",
  Rust = "Rust",
  Elm = "Elm",
  CakeML = "CakeML",
  Lean = "Lean",
  FSharp = "FSharp",
  Koka = "Koka"
}

// Reasons keyed by the name of a test configuration, as the runner prints it
// (e.g. "Rust", "Rust-untyped", "WebAssembly-cps")
export type Expectations = { [config: string]: string };

export type TestCase = {
  // Path to file containing the program lambda box source
  src: string,
  // Path to file containg the typed lambda box source. A test without one
  // fails on the typed configurations (Rust, Elm, Rust-verb, Rust-i64,
  // Rust-hybrid), where it must be marked as an expected failure
  tsrc?: string,
  // Name of the programs main function
  // Only used for typed backends where there isn't an explicit main function
  main: string,
  // The return type of the main function
  // Used to generate printing function for the output
  output_type: ProgramType,
  // The expected outputs: of the OCaml, C, LLVM, Wasm, CakeML, Lean, F# and
  // Koka drivers, of the Rust driver, and of the Elm driver
  expected_output: string[],
  // Types of the main functions parameters
  parameters?: ProgramType[],
  // Arguments for main function call
  arguments?: string[],
  // Extra flags and args for compiling the test program
  compiler_args?: string,
  // Attribute files per backend, passed with --attributes
  attributes?: Partial<Record<Lang, string>>,
  // Known failures, per configuration: the reason, which names an open issue
  // (#N or owner/repo#N). The test runs and must fail: if it passes, the
  // suite fails, so that the mark is removed
  xfail?: Expectations,
  // The typed backends (Rust, Elm) must reject the untyped `src` with "Could
  // not infer types". `true`: the program cannot be ML-typed, so rejecting it
  // is correct. A string: the program uses a feature that the typed backends
  // lack, and the string is the reason, which names the open issue of that
  // limitation, as for `xfail`
  rejected?: true | string,
  // The program has cofixpoints: C, Wasm, LLVM, OCaml, CakeML, Lean, F# and Koka must reject it
  // without --lower-cofix
  cofix?: boolean,
  // The expected output of the Rust-i64 test configuration, where nat is i64
  // and bool is the Rust bool, and of Rust-hybrid; a test without one fails there
  rust_i64_output?: string,
}

// Test configuration consisting of a target language, testset name, and a set of options
// for the peregrine compiler.
// The optional flag makes the typed backends (Rust, Elm) compile the untyped
// source `src` of each test, inferring its types, instead of `tsrc`.
// For Rust, the optional verb (`rust`, `rust-i64`) compiles with that verb
// instead of `peregrine compile` and src/rust/config.sexp.
export type TestConfiguration = [Lang, string, string, boolean?, string?]
