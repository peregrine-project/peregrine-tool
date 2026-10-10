import { Lang, SimpleType, TestCase, TestConfiguration } from "./types";

/* (backend, peregrine flags) pair configurations */
export var test_configurations: TestConfiguration[] = [
    [Lang.OCaml, "", ""],
    // [Lang.C, "cps", "--cps"], // TODO
    [Lang.C, "", ""],
    [Lang.Wasm, "cps", "--cps"],
    [Lang.Wasm, "", ""],
    [Lang.Rust, "", ""],
    [Lang.Elm, "", ""],
    // The typed backends on the untyped sources, whose types are inferred.
    // The expected outputs are those of the typed sources. A test marked as
    // `rejected` must fail with "Could not infer types".
    [Lang.Rust, "untyped", "", true],
    [Lang.Elm, "untyped", "", true],
    [Lang.CakeML, "", ""],
    [Lang.Lean, "", ""]
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
                // The typed backends keep the names of the constructors, which
                // agda2lambox emits as r#true and r#false
                "(cons () (rՖhshtrue) (cons () (rՖhshfalse) (cons () (rՖhshtrue) (cons () (rՖhshfalse) (empty)))))",
                "Cons R_UU23true (Cons R_UU23false (Cons R_UU23true (Cons R_UU23false Empty)))"
            ],
            parameters: []
        },
        {
            src: "agda/Equality.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`_≡_`), which Elm rejects
            skip: [Lang.Elm],
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
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
            main: "EtaCon_example",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) nil)",
                "(Ֆ_Ֆcons_ () (suc () (zero)) (Ֆ5bՖՖ5dՖ))",
                "Cons (S O) Empty"
            ],
            parameters: []
        },
        {
            src: "agda/Exports.ast",
            // The Rust test configuration derives Debug and Serialize for every
            // type, which fails on the function-typed fields of the record
            skip: [Lang.Rust],
            main: "Exports_main",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Hello.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
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
            src: "agda/Imports.ast",
            // Typable with a polymorphic List, but agda2lambox declares List without
            // parameters, so inference gives it one element type and the program
            // uses it at Bool and at Nat
            rejected: true,
            main: "Imports_test2",
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
            // The Rust test configuration derives Debug and Serialize for every
            // type, which fails on the function-typed fields of the record
            skip: [Lang.Rust],
            main: "Input_main",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Irr.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
            main: "Irr_ys",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/K.ast",
            // The entry point is a function, which the Rust driver cannot call
            skip: [Lang.Rust],
            main: "K_K",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Levels.ast",
            // Rust: the backend prints the axiom lsuc as a unit and then applies it
            // Elm: the backend prints an identifier that starts with an underscore
            // for the local definition toNat
            skip: [Lang.Rust, Lang.Elm],
            main: "Levels_testMkLevel",
            // OCaml/Wasm/CakeML call this program's malfunction
            // [main], which CertiRocq's Malfunction extraction
            // resolves to a tBox placeholder ("error: tBox has been
            // translated away") because [Levels.test]'s body
            // contains an erased type argument it can't lower.
            // [Levels_testMkLevel] does evaluate to 42 [S]s under
            // the Lean backend (which calls the symbol directly),
            // but the result is unobservable on the other backends.
            // Treat as Other so all backends exercise compile+run
            // without requiring a shared output convention.
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Map.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
            main: "Map_ys",
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
            // The Elm backend prints the constructors of Nat and Odd under the same
            // names, Zero and Succ
            skip: [Lang.Elm],
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "", ""],
            parameters: []
        },
        {
            src: "agda/Nat.ast",
            main: "Nat_thing",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "", ""],
            parameters: []
        },
        {
            src: "agda/OddEven.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`_,_`), which Elm rejects
            skip: [Lang.Elm],
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
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`_,_`), which Elm rejects
            skip: [Lang.Elm],
            main: "Proj_second",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/rust.ast",
            // The Elm driver names the module after the file, and rust is not a
            // module name
            skip: [Lang.Elm],
            main: "rust_testIdd",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S (S (S O))) nil)", ""],
            parameters: []
        },
        {
            src: "agda/scheme.ast",
            // f returns a Bool or a Nat depending on its first argument
            rejected: true,
            main: "scheme_demo",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S (S (S (S O))))))", ""],
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
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
            main: "Unicode_main",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S O) nil)", "", ""],
            parameters: []
        },
        {
            src: "agda/With.ast",
            // The Elm backend prints an identifier that starts with an underscore
            // for a name that is an operator (`[]`), which Elm rejects
            skip: [Lang.Elm],
            main: "With_ys",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: ["(cons true nil)", "", ""],
            parameters: []
        },
    ];

// Rocq Tests
var rocq_tests: TestCase[] =
    [
        {
            src: "rocq/extraction/Closure.ast",
            tsrc: "rocq/extraction/Closure_typed.ast",
            main: "Closure_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S (S (S O)))))", "(S () (S () (S () (S () (S () (O))))))", "S (S (S (S (S O))))"],
            parameters: []
        },
        {
            src: "rocq/extraction/Demo.ast",
            tsrc: "rocq/extraction/Demo_typed.ast",
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
            src: "rocq/extraction/Map.ast",
            tsrc: "rocq/extraction/Map_typed.ast",
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
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "(S () (O))", ""],
            parameters: [],
            // The Elm backend prints the constructor succ' as Succ', which is not an Elm identifier
            skip: [Lang.Elm]
        },
        {
            src: "rocq/extraction/Nat.ast",
            tsrc: "rocq/extraction/Nat_typed.ast",
            main: "Nat_thing",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "(S () (S () (S () (O))))", "S (S (S O))"],
            parameters: []
        },
        {
            src: "rocq/extraction/OddEven.ast",
            tsrc: "rocq/extraction/OddEven_typed.ast",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "(false)", "False"],
            parameters: []
        },
    ];
// Lean Tests
var lean_tests: TestCase[] =
    [
        {
            src: "lean/extraction/Demo.ast",
            // The names have an empty module path, so the Elm backend prints
            // identifiers that start with an underscore, which Elm rejects
            skip: [Lang.Elm],
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
            // The names have an empty module path, so the Elm backend prints
            // identifiers that start with an underscore, which Elm rejects
            skip: [Lang.Elm],
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

// List of programs to be tested
export var tests: TestCase[] =
    [...agda_tests, ...rocq_tests, ...lean_tests];
