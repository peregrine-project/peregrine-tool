all: multiple.vo multiple main

multiple.vo:
	rocq compile multiple.v

multiple: multiple.vo
	ocamlopt -c multiple.mli
	malfunction cmx multiple.mlf

main: main.ml multiple
	ocamlopt -c main.ml
	ocamlopt -o main multiple.cmx main.cmx 
	./main

.PHONY: main
