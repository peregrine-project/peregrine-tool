(lang dune 3.17)

(name rocq-peregrine)

(generate_opam_files false)

(source
 (github peregrine-project/peregrine-tool))

(authors "The Peregrine team")

(maintainers "The Peregrine team")

(license MIT)

(package
 (name rocq-peregrine)
 (synopsis "A framework for extracting lambda box programs")
 (description "A framework for extracting lambda box programs")
 (depends ocaml coq-primitive)
 (tags
  ("keyword:extraction" "logpath:Peregrine")))
