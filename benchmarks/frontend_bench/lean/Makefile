LAKE := lake
.PHONY: all clean check compile-c

C_RUNTIME_PATH?=$(shell coqc -where)/user-contrib/CertiCoq/Plugin/runtime/
GLUE?=../c_wrapper/glue.c ../c_wrapper/main.c
EXTRA_C?=eq_rec.c
OCAML_WRAPPER?=../ocaml_wrapper

all: check

ast:
	mkdir -p ast
bin:
	mkdir -p bin
bin/c: bin
	mkdir -p bin/c
bin/ocaml: bin
	mkdir -p bin/ocaml

bin/c/%.c: ast/%.ast bin/c
	peregrine c $< -o $@ --attributes=eq_rec_c.attr
	sed -i.tmp "s/bin\/c\///" $@

bin/c/%: bin/c/%.c
	gcc -o $@ -w -Wno-everything -O2 -fomit-frame-pointer -I. ${EXTRA_C} -I\${C_RUNTIME_PATH} \${C_RUNTIME_PATH}/gc_stack.c $< ${GLUE}

compile-c: check bin/c/BinaryTrees bin/c/Sieve bin/c/Quicksort bin/c/Fannkuch bin/c/Arith

bin/ocaml/%.mlf: ast/%.ast bin/ocaml
	peregrine ocaml $< -o $@

bin/ocaml/Axioms.cmi:
	cp Axioms.mli bin/ocaml/Axioms.mli
	ocamlopt -c bin/ocaml/Axioms.mli

bin/ocaml/Axioms.cmx: bin/ocaml/Axioms.cmi
	cp Axioms.ml bin/ocaml/Axioms.ml
	ocamlopt -I bin/ocaml -c bin/ocaml/Axioms.ml

bin/ocaml/%: bin/ocaml/%.mlf bin/ocaml/Axioms.cmx
	cp ../ocaml_wrapper/bench.mli $@.mli
	sed "s/{{NAME}}/$(shell basename $@)/g" ../ocaml_wrapper/main.ml > $@_main.ml
	ocamlopt -I ${OCAML_WRAPPER} -c $@.mli
	(cd bin/ocaml && malfunction cmx $*.mlf)
	ocamlopt -I ${OCAML_WRAPPER} -I bin/ocaml -c $@_main.ml
	ocamlopt -o $@ ${OCAML_WRAPPER}/types.cmx bin/ocaml/Axioms.cmx $@.cmx $@_main.cmx

compile-ocaml: check bin/ocaml/BinaryTrees bin/ocaml/Sieve bin/ocaml/Quicksort bin/ocaml/Fannkuch bin/ocaml/Arith


check: ast
	$(LAKE) build

clean:
	rm -rf ast/
	rm -rf bin/
	lake clean
