import { Lang, ProgramType, SimpleType, TestCase, TestConfiguration } from "./types";

/* (backend, peregrine flags) pair configurations */
export var test_configurations: TestConfiguration[] = [
    [Lang.OCaml, "", ""],
    [Lang.C, "cps", "--cps"],
    [Lang.C, "", ""],
    [Lang.Wasm, "cps", "--cps"],
    [Lang.Wasm, "", ""],
    [Lang.LLVM, "", ""],
    [Lang.Rust, "", ""],
    [Lang.Elm, "", ""],
    // The typed backends on the untyped sources, whose types are inferred.
    // The expected outputs are those of the typed sources. A test marked as
    // `rejected` must fail with "Could not infer types".
    [Lang.Rust, "untyped", "", true],
    [Lang.Elm, "untyped", "", true],
    // The Rust verbs other than `peregrine compile`. The dearg flags match
    // src/rust/config.sexp, so the rust verb expects the outputs of the Rust tests.
    [Lang.Rust, "verb", "--dearg-ctors false --dearg-consts false", false, "rust"],
    [Lang.Rust, "i64", "--dearg-ctors false --dearg-consts false", false, "rust-i64"],
    // i64 or GMP per value: prints as rust-i64 does
    [Lang.Rust, "hybrid", "--dearg-ctors false --dearg-consts false", false, "rust-hybrid"],
    // Reference counting instead of the arena, with the numbers of the rust
    // verb: serde prints an Rc<T> as T, so it expects the outputs of the Rust tests
    [Lang.Rust, "rc", "--dearg-ctors false --dearg-consts false", false, "rust --memory=rc"],
    [Lang.CakeML, "", ""],
    [Lang.Lean, "", ""],
    // The F# backend is experimental
    [Lang.FSharp, "experimental", ""],
    // The Koka backend is experimental
    [Lang.Koka, "experimental", ""],
    // The two optional middle-end passes, which only the untyped pipeline runs
    [Lang.OCaml, "passes", "--specialize-instances true --cse true"],
    // The lowering of cofixpoints, a no-op on the programs without them
    [Lang.OCaml, "cofix", "--lower-cofix true"],
    [Lang.C, "cofix", "--lower-cofix true"],
    [Lang.Wasm, "cofix", "--lower-cofix true"]
];

// The expected outputs of an Agda program that computes the natural number n,
// as the OCaml, C and Wasm drivers, the Rust driver and the Elm driver print it
function agda_nat(n: number): string[] {
    return [
        "(S ".repeat(n) + "O" + ")".repeat(n),
        "(suc () ".repeat(n) + "(zero)" + ")".repeat(n),
        n === 0 ? "Zero" : "Suc (".repeat(n - 1) + "Suc Zero" + ")".repeat(n - 1)
    ];
}

// An Agda program of the agda2lambox test suite whose entry point `test`
// computes the natural number n. The programs of test/typed and
// test/agda2rust are compiled with --typed, and the untyped backends take
// the same file; those of test/untyped get their typed source from
// with_typed_agda.
function agda_nat_test(name: string, n: number, typed: boolean): TestCase {
    return {
        src: `agda/${name}.ast`,
        tsrc: typed ? `agda/${name}.ast` : undefined,
        main: `${name}_test`,
        output_type: SimpleType.Nat,
        expected_output: agda_nat(n),
        rust_i64_output: typed ? agda_nat(n)[1] : undefined,
        parameters: []
    };
}

// The fields of a test of agda-src/ whose entry point is `digest`
function agda_digest(name: string, output_type: ProgramType, expected_output: string[]) {
    return { main: `${name}_digest`, output_type, expected_output, rust_i64_output: expected_output[1], parameters: [] };
}

// The attribute files of the backends, which realise the remapped constants of
// Remap and the postulate of Postulates
const remap_attributes: TestCase["attributes"] = {
    [Lang.OCaml]: "src/ocaml/remap.sexp",
    [Lang.C]: "src/c/remap.sexp",
    [Lang.LLVM]: "src/c/remap.sexp",
    [Lang.Wasm]: "src/c/remap.sexp",
    [Lang.Rust]: "src/rust/remap.sexp",
    [Lang.Elm]: "src/elm/remap.sexp",
    [Lang.Lean]: "src/lean/remap.sexp",
    [Lang.FSharp]: "src/fsharp/remap.sexp",
    [Lang.Koka]: "src/koka/remap.sexp"
};

// Known failures shared by several tests, by configuration
const on = (configs: string[], reason: string) => Object.fromEntries(configs.map((c) => [c, reason]));
const elm = (reason: string) => on(["Elm", "Elm-untyped"], reason);
const rust = (reason: string) => on(["Rust", "Rust-untyped", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"], reason);
const elm_operator = elm("#79: Elm prints the names of operators and of other symbols ([], _∷_, ×, ℕ) with a leading underscore, which Elm rejects");
const elm_ctor_clash = elm("#99: Elm prints the constructors of different types under the same name");
const elm_module_clash = elm("#94: the Elm module is named after the file, which clashes with a module of the Elm core or test library");
const rust_fn_fields = on(["Rust", "Rust-untyped", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"],
    "#79: Debug and Serialize are derived for every type, which fails on the function-typed fields of the record (E0277)");
const lean_untyped = on(["Rust", "Elm", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"],
    "peregrine-project/lean-to-lambdabox#21: the Lean frontend has no typed output, so a Lean program has no typed source");
const lean_name_clash = on(["Lean", "FSharp-experimental", "Koka-experimental"],
    "#93, #99: two definitions whose module paths differ only in their last component (where-modules, record modules) get the same name: agda2lambox writes module paths outermost first, and the backend keeps only one component");

// Agda Tests
var agda_tests: TestCase[] =
    [
        {
            src: "agda/Demo.ast",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "agda/Equality.ast",
            xfail: { "Elm": "#79: Elm prints the type name ≡ as __UU002261_, which Elm rejects" },
            main: "Equality_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S O))",
                "(suc () (suc () (zero)))",
                "Suc (Suc Zero)"
            ],
            parameters: []
        },
        {
            src: "agda/EtaCon.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "EtaCon_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) nil)",
                "(Ֆ_Ֆcons_ () (suc () (zero)) (ՖՖ5bՖՖ5d))",
                "Cons (S O) Empty"
            ],
            parameters: []
        },
        {
            src: "agda/Hello.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "Hello_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))",
                "(Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero)))))))))))))))))))))))))))))))))) (ՖՖ5bՖՖ5d)))))))",
                "Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))))))))))))))))))))))))) Empty)))))"
            ],
            parameters: []
        },
        {
            src: "agda/Imports.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "Imports_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S O)))))) nil)",
                "(Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))) (ՖՖ5bՖՖ5d))",
                "Cons (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) Empty"
            ],
            parameters: []
        },
        agda_nat_test("K", 42, false),
        {
            src: "agda/Lvls.ast",
            xfail: {
                ...elm("#99: agda2lambox writes the module path of the where-bound toNat outermost first, so Elm prints it as _50_Lvls_toNat, which Elm rejects")
            },
            main: "Lvls_test",
            output_type: SimpleType.Nat,
            expected_output: agda_nat(210),
            parameters: []
        },
        {
            src: "agda/Map.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "Map_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "(Ֆ_Ֆcons_ () (suc () (suc () (zero))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))) (Ֆ_Ֆcons_ () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (suc () (zero))))))))))) (ՖՖ5bՖՖ5d))))",
                "Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))) Empty))"
            ],
            parameters: []
        },
        {
            src: "agda/Mutual.ast",
            xfail: elm("#99: Elm prints the constructors of Nat and Odd under the same names, Zero and Succ"),
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S O)",
                "(succ () (zero))",
                "Succ Zero"
            ],
            parameters: []
        },
        {
            src: "agda/Nat.ast",
            main: "Nat_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S (S O)))",
                "(suc () (suc () (suc () (zero))))",
                "Suc (Suc (Suc Zero))"
            ],
            parameters: []
        },
        {
            src: "agda/OddEven.ast",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: [
                "false",
                "(false)",
                "False"
            ],
            parameters: []
        },
        {
            src: "agda/PatternLambda.ast",
            main: "PatternLambda_test",
            output_type: SimpleType.Bool,
            expected_output: [
                "false",
                "(false)",
                "False"
            ],
            parameters: []
        },
        {
            src: "agda/Proj.ast",
            xfail: elm("#79: Elm prints the operator name _,_ as __UU2c_, which Elm rejects"),
            main: "Proj_test",
            output_type: SimpleType.Bool,
            expected_output: [
                "false",
                "(false)",
                "False"
            ],
            parameters: []
        },
        {
            src: "agda/rust.ast",
            xfail: elm("#94: the Elm module is named after the file, and rust is not a module name"),
            main: "rust_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S O))) nil)",
                "(Ֆ_ՖՖ3aՖՖ3a_ () (suc () (suc () (suc () (zero)))) (ՖՖ5bՖՖ5d))",
                "Cons (Suc (Suc (Suc Zero))) Empty"
            ],
            parameters: []
        },
        {
            src: "agda/STLC.ast",
            // The type of the result of eval depends on the type of the term
            rejected: true,
            xfail: {
                ...on(["Rust", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"], "#127: the branches of eval have different types (the type of the value is indexed by the type of the term), and the Rust printer has no cast (E0308)"),
                "Elm": "#79: Elm prints the type name ∋ as __UU00220b_, which Elm rejects"
            },
            main: "STLC_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S O))",
                "(suc () (suc () (zero)))",
                "Suc (Suc Zero)"
            ],
            parameters: []
        },
        {
            src: "agda/Unicode.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "Unicode_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) nil)",
                "(Ֆ_Ֆcons_ () (suc () (zero)) (ՖՖ5bՖՖ5d))",
                "Cons (Suc Zero) Empty"
            ],
            parameters: []
        },
        {
            src: "agda/With.ast",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            main: "With_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true nil)",
                "(Ֆ_ՖՖ3aՖՖ3a_ () (true) (ՖՖ5bՖՖ5d))",
                "Cons True Empty"
            ],
            parameters: []
        },
        // Untyped
        agda_nat_test("ErasedRecursion", 2, false),
        { ...agda_nat_test("Fannkuch", 7, false), xfail: elm_operator },
        {
            ...agda_nat_test("InductionRecursion", 3, false),
            // An ML type exists, but inference gives the first argument of the
            // constructor _∷_⊣_ (the index αs) the type box
            rejected: "#79: type inference cannot unify the type of _∷_⊣_ with its application to a list",
            xfail: { "Elm": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" }
        },
        { ...agda_nat_test("Params", 25, false), xfail: elm_operator },
        { ...agda_nat_test("Prelude", 42, false), xfail: elm_operator },
        agda_nat_test("RecursiveInline", 6, false),
        agda_nat_test("StrictLet", 3, false),
        { ...agda_nat_test("Terminating", 6, false), xfail: elm("#99: agda2lambox writes the module path of a where-bound lambda outermost first, so Elm prints it as _14_Terminating__UU2eextendedlambda1, which Elm rejects") },
        { ...agda_nat_test("WhereNames", 6, false), xfail: { ...elm_operator, ...lean_name_clash } },
        // Typed: test/typed
        { ...agda_nat_test("Scheme", 42, true), xfail: elm_operator },
        { ...agda_nat_test("Test", 42, true), xfail: elm_module_clash },
        { ...agda_nat_test("Types", 42, true), xfail: elm_operator },
        // Typed: test/agda2rust
        agda_nat_test("Bool00", 168, true),
        agda_nat_test("Bool", 84, true),
        { ...agda_nat_test("ConsImplicitArgs", 168, true), xfail: elm_ctor_clash },
        agda_nat_test("Curry", 168, true),
        { ...agda_nat_test("Either", 42, true), xfail: elm_ctor_clash },
        agda_nat_test("ErasedFields", 168, true),
        agda_nat_test("EtaExpansion", 672, true),
        agda_nat_test("ExactSplit", 0, true),
        { ...agda_nat_test("Exp", 168, true), xfail: { ...rust("#127: the branches of geval have different types (GExp is indexed by the type of its value), and the Rust printer has no cast (E0308)"), ...elm_ctor_clash } },
        agda_nat_test("Identity", 42, true),
        { ...agda_nat_test("Levels", 294, true), xfail: elm("#99: agda2lambox writes the module path of the where-bound toNat outermost first, so Elm prints it as _50_Levels_toNat, which Elm rejects") },
        agda_nat_test("List0", 42, true),
        { ...agda_nat_test("List", 42, true), xfail: elm_module_clash },
        { ...agda_nat_test("Maybe", 42, true), xfail: elm_module_clash },
        agda_nat_test("MultiArgFun", 630, true),
        agda_nat_test("Newtype", 42, true),
        agda_nat_test("Numbers", 42, true),
        agda_nat_test("OpenModule", 210, true),
        { ...agda_nat_test("OverloadedFields", 168, true), xfail: { ...elm_ctor_clash, ...lean_name_clash } },
        { ...agda_nat_test("PartialApp", 378, true), xfail: elm_operator },
        agda_nat_test("PartialAppConst", 84, true),
        agda_nat_test("PartialAppId", 336, true),
        { ...agda_nat_test("PartialAppM", 378, true), xfail: elm_operator },
        agda_nat_test("PartialAppSwap", 210, true),
        agda_nat_test("PointFree", 126, true),
        // The postulate TODO is realised by the attribute files; it is only
        // reached in a branch that is not taken
        {
            ...agda_nat_test("Postulates", 84, true),
            attributes: remap_attributes,
            xfail: {
                ...on(["WebAssembly", "WebAssembly-cps", "WebAssembly-cofix"], "#126: the Wasm backend rejects a remapped constant (Unsupported primitive operator)"),
                "CakeML": "#126: the CakeML backend takes no constant remappings, so the postulate TODO is printed as a raise, which cake does not parse"
            }
        },
        agda_nat_test("Prim", 42, true),
        { ...agda_nat_test("Product", 42, true), xfail: elm_operator },
        { ...agda_nat_test("RecordFields", 168, true), xfail: elm_ctor_clash },
        { ...agda_nat_test("RunTimeIrrelevance", 336, true), xfail: elm("#94, #99: with the elm_false_elim_def of the test configuration, an absurd clause is printed as an empty branch, and the constructors Mk of two types clash") },
        agda_nat_test("Simplification", 42, true),
        agda_nat_test("Singleton", 42, true),
        agda_nat_test("Top", 42, true),
        { ...agda_nat_test("TypeAliases", 168, true), xfail: elm_operator },
        agda_nat_test("UnusedArgs", 84, true),
        { ...agda_nat_test("Where", 210, true), xfail: { ...elm_operator, ...lean_name_clash } },
    ];

// Rocq Tests
var rocq_tests: TestCase[] =
    [
        {
            // Dictionaries passed to a polymorphic function: the instance
            // specialization of the OCaml-passes configuration rewrites it
            src: "rocq/extraction/Classy.ast",
            tsrc: "rocq/extraction/Classy_typed.ast",
            xfail: {
                "Rust": "#79: the Rust test configuration derives Debug for every type, which fails on the function-typed fields of the records",
                "Rust-verb": "#79: the rust verb derives Debug for every type, which fails on the function-typed fields of the records",
                "Rust-rc": "#79: rust --memory=rc derives Debug for every type, which fails on the function-typed fields of the records",
                "Rust-i64": "#79: the rust-i64 verb derives Debug for every type, which fails on the function-typed fields of the records",
                "Rust-hybrid": "#79: the rust-hybrid verb derives Debug for every type, which fails on the function-typed fields of the records",
                "Elm-untyped": "#79: the inferred types give each record field a type variable instead of the function type"
            },
            rust_i64_output: "3",
            main: "Classy_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/Closure.ast",
            tsrc: "rocq/extraction/Closure_typed.ast",
            rust_i64_output: "5",
            main: "Closure_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S (S (S O)))))", "(S () (S () (S () (S () (S () (O))))))", "S (S (S (S (S O))))"],
            parameters: []
        },
        {
            src: "rocq/extraction/CoStream.ast",
            main: "CoStream_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons O (cons (S O) (cons O (cons (S O) nil))))",
                "(cons () (O) (cons () (S () (O)) (cons () (O) (cons () (S () (O)) (nil)))))",
                "Cons O (Cons (S O) (Cons O (Cons (S O) Nil)))"
            ],
            parameters: [],
            cofix: true,
            tsrc: "rocq/extraction/CoStream_typed.ast",
            rust_i64_output: "(cons () 0 (cons () 1 (cons () 0 (cons () 1 (nil)))))",
            rejected: "#125: the Rust and Elm printers do not support cofixpoints, so neither does type inference",
            xfail: on(["Rust", "Elm", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"], "#125: the Rust and Elm printers do not support cofixpoints (Cannot handle tCoFix)")
        },
        {
            src: "rocq/extraction/Prims.ast",
            main: "Prims_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) (cons O nil))",
                "(cons () (S () (O)) (cons () (O) (nil)))",
                "Cons (S O) (Cons O Nil)"
            ],
            parameters: [],
            tsrc: "rocq/extraction/Prims_typed.ast",
            rust_i64_output: "(cons () 1 (cons () 0 (nil)))",
            rejected: "#125: the Rust and Elm printers do not support primitive values, so neither does type inference",
            xfail: {
                "Elm": "#125: the Elm printer does not support primitive values (Cannot handle Rocq primitive types)",
                "WebAssembly": "#125: the Wasm backend does not support primitive strings",
                "WebAssembly-cps": "#125: the Wasm backend does not support primitive strings",
                "WebAssembly-cofix": "#125: the Wasm backend does not support primitive strings",
                "CakeML": "#125: the CakeML backend prints every primitive literal as a raise"
            }
        },
        {
            src: "rocq/extraction/Demo.ast",
            tsrc: "rocq/extraction/Demo_typed.ast",
            rust_i64_output: "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                // The Rust backend keeps the names of the constructors, which are lower case in Demo.v
                "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Hello.ast",
            tsrc: "rocq/extraction/Hello_typed.ast",
            rust_i64_output: "(cons () 72 (cons () 101 (cons () 108 (cons () 108 (cons () 111 (cons () 33 (nil)))))))",
            main: "Hello_hello",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))",
                "(cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O)))))))))))))))))))))))))))))))))) (nil)))))))",
                "Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) Nil)))))"
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Remap.ast",
            tsrc: "rocq/extraction/Remap_typed.ast",
            rust_i64_output: "3",
            attributes: remap_attributes,
            xfail: {
                ...on(["WebAssembly", "WebAssembly-cps", "WebAssembly-cofix"], "#126: the Wasm backend rejects a remapped constant (Unsupported primitive operator)"),
                "CakeML": "#126: the CakeML backend takes no constant remappings, so the axiom ext_id is printed as a raise, which cake does not parse",
                "Rust-untyped": "#79: inference prints no method for the axiom ext_id, and gives the unused parameter of shadowed the type ()",
                "Elm-untyped": "#126: Elm prints shadowed, with its body, under the remapped name identity, so the program calls it instead of Basics.identity"
            },
            main: "Remap_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/EtaFix.ast",
            tsrc: "rocq/extraction/EtaFix_typed.ast",
            rust_i64_output: "8",
            main: "EtaFix_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S (S (S (S (S (S (S O))))))))",
                "(S () (S () (S () (S () (S () (S () (S () (S () (O)))))))))",
                "S (S (S (S (S (S (S (S O)))))))"
            ],
            parameters: []
        },
        {
            // Corelib's id is declared through a type alias (benchmarks UPSTREAM_ISSUES entry 3)
            src: "rocq/extraction/Id.ast",
            tsrc: "rocq/extraction/Id_typed.ast",
            // The Elm backend has the same defect and no stopgap
            xfail: { "Elm": "#84: id is printed without its type parameter" },
            rust_i64_output: "(cons () 1 (cons () 2 (nil)))",
            main: "Id_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) (cons (S (S O)) nil))",
                "(cons () (S () (O)) (cons () (S () (S () (O))) (nil)))",
                "Cons (S O) (Cons (S (S O)) Nil)"
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Map.ast",
            tsrc: "rocq/extraction/Map_typed.ast",
            rust_i64_output: "(cons () () 2 (cons () () 6 (cons () () 10 (nil () ()))))",
            main: "Map_ys",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "(cons () () (S () (S () (O))) (cons () () (S () (S () (S () (S () (S () (S () (O))))))) (cons () () (S () (S () (S () (S () (S () (S () (S () (S () (S () (S () (O))))))))))) (nil () ()))))",
                "Cons () (S (S O)) (Cons () (S (S (S (S (S (S O)))))) (Cons () (S (S (S (S (S (S (S (S (S (S O)))))))))) (Nil ())))"
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Mutual.ast",
            tsrc: "rocq/extraction/Mutual_typed.ast",
            rust_i64_output: "1",
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "(S () (O))", "S O"],
            parameters: [],
            xfail: {
                "Elm": "#99: Elm prints the constructor succ' as Succ', which is not an Elm identifier",
                "Elm-untyped": "#99: Elm prints the constructor succ' as Succ', which is not an Elm identifier"
            }
        },
        {
            src: "rocq/extraction/Nat.ast",
            tsrc: "rocq/extraction/Nat_typed.ast",
            rust_i64_output: "3",
            main: "Nat_thing",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/OddEven.ast",
            tsrc: "rocq/extraction/OddEven_typed.ast",
            rust_i64_output: "(false)",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "(false)", "False"],
            parameters: []
        },
        {
            src: "rocq/extraction/OpenCase.ast",
            tsrc: "rocq/extraction/OpenCase_typed.ast",
            rust_i64_output: "3",
            main: "OpenCase_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/Params.ast",
            tsrc: "rocq/extraction/Params_typed.ast",
            rust_i64_output: "3",
            main: "Params_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/Phantom.ast",
            tsrc: "rocq/extraction/Phantom_typed.ast",
            rust_i64_output: "1",
            main: "Phantom_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "(S () (O))", "S O"],
            parameters: []
        },
        {
            src: "rocq/extraction/PolyLet.ast",
            tsrc: "rocq/extraction/PolyLet_typed.ast",
            rust_i64_output: "2",
            // A let-bound polymorphic function used at two types: Rocq's
            // extraction generalises the let, the type inference does not
            rejected: "#79: the type inference does not generalise let-bound definitions",
            xfail: on(["Rust", "Rust-verb", "Rust-i64", "Rust-hybrid", "Rust-rc"], "#127: the Rust printer binds the polymorphic id with a let, as a closure of a single type, so its uses at bool and at nat do not type-check (E0308)"),
            main: "PolyLet_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S O))",
                "(S () (S () (O)))",
                "S (S O)"
            ],
            parameters: []
        },
    ];
// Lean Tests
var lean_tests: TestCase[] =
    [
        {
            src: "lean/extraction/Demo.ast",
            xfail: { ...lean_untyped, "Elm-untyped": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects" },
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotempty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "lean/extraction/Map.ast",
            xfail: { ...lean_untyped, "Elm-untyped": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects" },
            main: "Map_ys",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "(List_Ֆdotcons () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotzero))) (List_Ֆdotcons () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotzero))))))) (List_Ֆdotcons () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotsuc () (Nat_Ֆdotzero))))))))))) (List_Ֆdotempty))))",
                "Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) (Cons (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))) Empty))"
            ],
            parameters: []
        }, // Generates invalid identifier names in C backend
    ];

// The Demo programs given to peregrine as proof-assistant sources: peregrine
// runs the frontend, which must be installed, and asks it for typed lambda
// box for the typed backends. They expect the outputs of the Demo tests above.
var source_tests: TestCase[] =
    [
        {
            src: "rocq/theories/Demo.v",
            tsrc: "rocq/theories/Demo.v",
            // The load path of rocq/_CoqProject, without its plugin paths: they
            // name the plugin of the source tree, which CI does not build
            // (CI compiles rocq/ with _CoqProject.ci)
            compiler_args: "--entry test --frontend-arg=-Q --frontend-arg=rocq/theories --frontend-arg=Peregrine.Tests",
            rust_i64_output: "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "agda-src/Demo.agda",
            tsrc: "agda-src/Demo.agda",
            rust_i64_output: "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(cons () (true) (cons () (false) (cons () (true) (cons () (false) (empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            // agda2lambox's Exports, whose entry point is a record of
            // functions, with an entry point that uses the record
            src: "agda-src/Exports.agda",
            tsrc: "agda-src/Exports.agda",
            xfail: rust_fn_fields,
            ...agda_digest("Exports", SimpleType.Nat, agda_nat(2))
        },
        {
            // agda2lambox's Irr, whose entry point is a vector, with an entry
            // point that turns it into a list
            src: "agda-src/Irr.agda",
            tsrc: "agda-src/Irr.agda",
            xfail: elm("#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects"),
            ...agda_digest("Irr", { type: "list", a_t: SimpleType.Nat }, [
                "(cons (S (S O)) (cons (S O) nil))",
                "(Ֆ_Ֆcons_ () (suc () (suc () (zero))) (Ֆ_Ֆcons_ () (suc () (zero)) (ՖՖ5bՖՖ5d)))",
                "Cons (Suc (Suc Zero)) (Cons (Suc Zero) Empty)"
            ])
        },
        {
            // agda2lambox's Input, likewise
            src: "agda-src/Input.agda",
            tsrc: "agda-src/Input.agda",
            xfail: rust_fn_fields,
            ...agda_digest("Input", SimpleType.Bool, ["true", "(true)", "True"])
        },
        {
            // Lean has no typed output: the typed backends infer the types
            src: "lean/source/Demo.lean",
            tsrc: "lean/source/Demo.lean",
            compiler_args: "--entry test",
            xfail: {
                "Elm": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects",
                "Elm-untyped": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects"
            },
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotempty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            rust_i64_output: "(List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotcons () (Bool_Ֆdottrue) (List_Ֆdotcons () (Bool_Ֆdotfalse) (List_Ֆdotempty)))))",
            parameters: []
        },
    ];

// The programs of agda2lambox's test/untyped are also compiled with --typed,
// to agda/typed/ (see .github/workflows/build.yml). Agda's Nat and Bool are
// not Rocq's, so rust-i64 prints them as the Rust tests do.
function with_typed_agda(t: TestCase): TestCase {
    return t.tsrc !== undefined ? t : { ...t, tsrc: t.src.replace(/^agda\//, "agda/typed/"), rust_i64_output: t.rust_i64_output ?? t.expected_output[1] };
}

// List of programs to be tested
export var tests: TestCase[] =
    [...agda_tests.map(with_typed_agda), ...rocq_tests, ...lean_tests, ...source_tests];
