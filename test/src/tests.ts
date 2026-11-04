import { Lang, SimpleType, TestCase, TestConfiguration } from "./types";

/* (backend, peregrine flags) pair configurations */
export var test_configurations: TestConfiguration[] = [
    [Lang.OCaml, "", ""],
    // [Lang.C, "cps", "--cps"], // TODO
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
    [Lang.CakeML, "", ""],
    [Lang.Lean, "", ""],
    // The F# backend is experimental
    [Lang.FSharp, "experimental", ""],
    // The Koka backend is experimental
    [Lang.Koka, "experimental", ""],
    // The two optional middle-end passes, which only the untyped pipeline runs
    [Lang.OCaml, "passes", "--specialize-instances true --cse true"],
    // The lowering of cofixpoints, which only the programs using them run
    [Lang.OCaml, "cofix", "--lower-cofix true"],
    [Lang.C, "cofix", "--lower-cofix true"],
    [Lang.Wasm, "cofix", "--lower-cofix true"]
];

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
            main: "Equality_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S O))",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/EtaCon.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
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
            src: "agda/Exports.ast",
            xfail: { "Rust-untyped": "#79: the Rust test configuration derives Debug for every type, which fails on the function-typed fields of the record" },
            main: "Exports_test",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Hello.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "Hello_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Imports.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "Imports_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S O)))))) nil)",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Input.ast",
            xfail: { "Rust-untyped": "#79: the Rust test configuration derives Debug for every type, which fails on the function-typed fields of the record" },
            main: "Input_test",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Irr.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "Irr_test",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/K.ast",
            main: "K_test",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Lvls.ast",
            xfail: {
                "Rust-untyped": "#79: the projection of the erased field ℓ is printed as a unit, which is then applied",
                "Elm-untyped": "#79: Elm prints the local definition toNat as _50_Lvls_toNat, which Elm rejects"
            },
            main: "Lvls_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S ".repeat(210) + "O" + ")".repeat(210), "", ""],
            parameters: []
        },
        {
            src: "agda/Map.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "Map_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Mutual.ast",
            xfail: { "Elm-untyped": "#99: Elm prints the constructors of Nat and Odd under the same names, Zero and Succ" },
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "", ""],
            parameters: []
        },
        {
            src: "agda/Nat.ast",
            main: "Nat_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "", ""],
            parameters: []
        },
        {
            src: "agda/OddEven.ast",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/PatternLambda.ast",
            main: "PatternLambda_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/Proj.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name _,_ as __UU2c_, which Elm rejects" },
            main: "Proj_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/rust.ast",
            xfail: { "Elm-untyped": "#94: the Elm module is named after the file, and rust is not a module name" },
            main: "rust_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S (S (S O))) nil)", ""],
            parameters: []
        },
        /*     {
                tsrc: "agda/SchemeTyped.ast",
                main: "SchemeTyped_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        {
            src: "agda/STLC.ast",
            // The type of the result of eval depends on the type of the term
            rejected: true,
            main: "STLC_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S O))", "", ""],
            parameters: []
        },
        /*     {
                tsrc: "agda/Test.ast",
                main: "Test_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        /*     {
                tsrc: "agda/Types.ast",
                main: "Types_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        {
            src: "agda/Unicode.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "Unicode_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S O) nil)", "", ""],
            parameters: []
        },
        {
            src: "agda/With.ast",
            xfail: { "Elm-untyped": "#79: Elm prints the operator name [] as _UU5b_UU5d, which Elm rejects" },
            main: "With_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: ["(cons true nil)", "", ""],
            parameters: []
        },
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
            // The typed backends do not support cofixpoints, and there is no
            // typed source
            rejected: true
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
            // The typed backends do not support primitive values, and there is
            // no typed source
            rejected: true,
            unsupported: {
                "WebAssembly": "the Wasm backend does not support primitive strings",
                "WebAssembly-cps": "the Wasm backend does not support primitive strings",
                "CakeML": "the CakeML backend does not support primitive values: it prints them as a raise"
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
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Remap.ast",
            unsupported: Object.fromEntries(["OCaml", "OCaml-passes", "C", "WebAssembly", "WebAssembly-cps", "LLVM",
                "Rust-untyped", "Elm-untyped", "CakeML", "Koka-experimental"].map((c) => [c, "the axiom ext_id needs a remapping, which the test supplies for Lean and F# only"])),
            configs: { [Lang.Lean]: "src/lean/remap.sexp", [Lang.FSharp]: "src/fsharp/remap.sexp" },
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
            expected_output: ["(S O)", "(S () (O))", ""],
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
            xfail: {
                "Rust": "rocq-typed-extraction#19: the typed Rust backend keeps the phantom parameter, which rustc cannot infer at the constructor",
                "Rust-verb": "rocq-typed-extraction#19: the typed Rust backend keeps the phantom parameter, which rustc cannot infer at the constructor",
                "Rust-i64": "rocq-typed-extraction#19: the typed Rust backend keeps the phantom parameter, which rustc cannot infer at the constructor",
                "Rust-hybrid": "rocq-typed-extraction#19: the typed Rust backend keeps the phantom parameter, which rustc cannot infer at the constructor"
            },
            rust_i64_output: "1",
            main: "Phantom_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "(S () (O))", "S O"],
            parameters: []
        },
        {
            src: "rocq/extraction/PolyLet.ast",
            // A let-bound polymorphic function used at two types: Rocq's
            // extraction generalises the let, the type inference does not
            rejected: true,
            main: "PolyLet_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S O))", "", ""],
            parameters: []
        },
    ];
// Lean Tests
var lean_tests: TestCase[] =
    [
        {
            src: "lean/extraction/Demo.ast",
            xfail: { "Elm-untyped": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects" },
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
            xfail: { "Elm-untyped": "#79: the names have an empty module path, so Elm prints identifiers that start with an underscore, which Elm rejects" },
            main: "Map_ys",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "",
                ""
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
            parameters: []
        },
    ];

// List of programs to be tested
export var tests: TestCase[] =
    [...agda_tests, ...rocq_tests, ...lean_tests, ...source_tests];
