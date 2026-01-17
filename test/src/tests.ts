import { Lang, SimpleType, TestCase, TestConfiguration } from "./types";

/* (backend, peregrine flags) pair configurations */
export var test_configurations: TestConfiguration[] = [
    [Lang.OCaml, "", ""],
    // [Lang.C, "cps", "--cps"], // TODO
    [Lang.C, "", ""],
    [Lang.Wasm, "cps", "--cps"],
    [Lang.Wasm, "", ""],
    // [Lang.Rust, "", "--attr=\"#[derive(Debug, Clone, Serialize)]\" --top-preamble=\"use lexpr::{to_string}; use serde_derive::{Serialize}; use serde_lexpr::{to_value};\n\""],
    // [Lang.Elm, "", "--top-preamble=\"import Test\nimport Html\nimport Expect exposing (Expectation)\""],
];

// List of programs to be tested
export var tests: TestCase[] = [
    // Exceeds stack size
    // { src: "agda/BigDemo.ast", main: "", output_type: { type: "list", a_t: SimpleType.Nat }, expected_output: "", parameters: [] },

    // No main in program
    // { src: "agda/EtaCon.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },
    // { src: "agda/Test.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },
    // { src: "agda/Types.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },


    {
        src: "agda/Demo.ast",
        tsrc: "agda/Demo.tast",
        main: "Demo_test",
        output_type: { type: "list", a_t: SimpleType.Bool },
        expected_output: [
            "(cons true (cons false (cons true (cons false (cons true nil)))))",
            "(Cons () (True) (Cons () (False) (Cons () (True) (Cons () (False) (Cons () (True) (Empty))))))",
            "Cons True (Cons False (Cons True (Cons False (Cons True Empty))))"
        ],
        parameters: []
    },
    {
        src: "agda/Demo2.ast",
        tsrc: "agda/Demo2.tast",
        main: "Demo2_test",
        output_type: { type: "list", a_t: { type: "list", a_t: SimpleType.Bool } },
        expected_output: [
            "(cons (cons true nil) (cons (cons false nil) nil))",
            "(Cons () (Cons () (True) (Empty)) (Cons () (Cons () (False) (Empty)) (Empty)))",
            "Cons (Cons True Empty) (Cons (Cons False Empty) Empty)"
        ],
        parameters: []
    },
    {
        src: "agda/Equality.ast",
        tsrc: "agda/Equality.tast",
        main: "Equality_test",
        output_type: SimpleType.Nat,
        expected_output: ["(S (S O))", ""],
        parameters: []
    },
    {
        src: "agda/Hello.ast",
        tsrc: "agda/Hello.tast",
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
        tsrc: "agda/Imports.tast",
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
        src: "agda/Irr.ast",
        tsrc: "agda/Irr.tast",
        main: "Irr_ys",
        output_type: SimpleType.Other,
        expected_output: undefined,
        parameters: []
    },
    {
        src: "agda/K.ast",
        tsrc: "agda/K.tast",
        main: "K_K",
        output_type: SimpleType.Other,
        expected_output: undefined,
        parameters: []
    },
    {
        src: "agda/Levels.ast",
        tsrc: "agda/Levels.tast",
        main: "Levels_testMkLevel",
        output_type: SimpleType.Nat,
        expected_output: [
            "(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))",
            "",
            ""
        ],
        parameters: []
    },
    {
        src: "agda/Map.ast",
        tsrc: "agda/Map.tast",
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
        tsrc: "agda/Mutual.tast",
        main: "Mutual_test",
        output_type: SimpleType.Nat,
        expected_output: ["(S O)", "", ""],
        parameters: []
    },
    {
        src: "agda/Nat.ast",
        tsrc: "agda/Nat.tast",
        main: "Nat_thing",
        output_type: SimpleType.Nat,
        expected_output: ["(S (S (S O)))", "", ""],
        parameters: []
    },
    {
        src: "agda/OddEven.ast",
        tsrc: "agda/OddEven.tast",
        main: "OddEven_test",
        output_type: SimpleType.Bool,
        expected_output: ["true", "", ""],
        parameters: []
    },
    {
        src: "agda/PatternLambda.ast",
        tsrc: "agda/PatternLambda.tast",
        main: "PatternLambda_test",
        output_type: SimpleType.Bool,
        expected_output: ["false", "", ""],
        parameters: []
    },
    {
        src: "agda/Proj.ast",
        tsrc: "agda/Proj.tast",
        main: "Proj_second",
        output_type: SimpleType.Bool,
        expected_output: ["false", "", ""],
        parameters: []
    },
    {
        src: "agda/STLC.ast",
        tsrc: "agda/STLC.tast",
        main: "STLC_test",
        output_type: SimpleType.Nat,
        expected_output: ["(S (S O))", "", ""],
        parameters: []
    },
    {
        src: "agda/With.ast",
        tsrc: "agda/With.tast",
        main: "With_ys",
        output_type: { type: "list", a_t: SimpleType.Bool },
        expected_output: ["(cons true nil)", "", ""],
        parameters: []
    },
];
