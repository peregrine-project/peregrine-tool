(lang dune 3.17)

(name rocq-lambda-box-extraction)

(generate_opam_files false)

(source
 (github AU-COBRA/lambda-box-extraction))

(authors "The COBRA team")

(maintainers "The COBRA team")

(license MIT)

(package
 (name rocq-lambda-box-extraction)
 (synopsis "A framework for extracting lambda box programs")
 (description "A framework for extracting lambda box programs")
 (depends ocaml coq-primitive)
 (tags
  ("keyword:extraction" "logpath:LambdaBox")))
