all: check
.PHONY: all compile-c

C_RUNTIME_PATH?=$(shell coqc -where)/user-contrib/CertiCoq/Plugin/runtime/
GLUE?=../c_wrapper/glue.c ../c_wrapper/main.c
OCAML_WRAPPER?=../ocaml_wrapper

ast:
	mkdir -p ast
bin:
	mkdir -p bin
bin/c: bin
	mkdir -p bin/c
bin/ocaml: bin
	mkdir -p bin/ocaml

bin/c/%.c: ast/%.ast bin/c
	peregrine c $< -o $@ --attributes=bool_reorder.attr
	sed -i.tmp "s/bin\/c\///" $@

bin/c/%: bin/c/%.c
	gcc -o $@ -w -Wno-everything -O2 -fomit-frame-pointer -I\${C_RUNTIME_PATH} \${C_RUNTIME_PATH}/gc_stack.c $< ${GLUE}

compile-c: check bin/c/BinaryTrees bin/c/Sieve bin/c/Quicksort bin/c/Fannkuch bin/c/Arith

bin/ocaml/%.mlf: ast/%.ast bin/ocaml
	peregrine ocaml $< -o $@ --attributes=bool_reorder.attr

bin/ocaml/%: bin/ocaml/%.mlf
	cp ../ocaml_wrapper/bench.mli $@.mli
	sed "s/{{NAME}}/$(shell basename $@)/g" ../ocaml_wrapper/main.ml > $@_main.ml
	ocamlopt -I ${OCAML_WRAPPER} -c $@.mli
	(cd bin/ocaml && malfunction cmx $*.mlf)
	ocamlopt -I ${OCAML_WRAPPER} -I bin/ocaml -c $@_main.ml
	ocamlopt -o $@ ${OCAML_WRAPPER}/types.cmx $@.cmx $@_main.cmx

compile-ocaml: check bin/ocaml/BinaryTrees bin/ocaml/Sieve bin/ocaml/Quicksort bin/ocaml/Fannkuch bin/ocaml/Arith


check: theory

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile ast
	+@make -f RocqMakefile
.PHONY: theory

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -rf ast/
	rm -rf bin/
.PHONY: clean
