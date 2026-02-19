AGDA2LAMBOX := agda2lambox
.PHONY: all clean check compile-c

C_RUNTIME_PATH?=$(shell coqc -where)/user-contrib/CertiCoq/Plugin/runtime/
GLUE?=../c_wrapper/glue.c ../c_wrapper/main.c
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
	peregrine c $< -o $@
	sed -i.tmp "s/bin\/c\///" $@

bin/c/%: bin/c/%.c
	gcc -o $@ -w -Wno-everything -O2 -fomit-frame-pointer -I\${C_RUNTIME_PATH} \${C_RUNTIME_PATH}/gc_stack.c $< ${GLUE}

compile-c: check bin/c/BinaryTrees bin/c/Sieve bin/c/Quicksort bin/c/Fannkuch bin/c/Arith

bin/ocaml/%.mlf: ast/%.ast bin/ocaml
	peregrine ocaml $< -o $@

bin/ocaml/%: bin/ocaml/%.mlf
	cp ../ocaml_wrapper/bench.mli $@.mli
	sed "s/{{NAME}}/$(shell basename $@)/g" ../ocaml_wrapper/main.ml > $@_main.ml
	ocamlopt -I ${OCAML_WRAPPER} -c $@.mli
	(cd bin/ocaml && malfunction cmx $*.mlf)
	ocamlopt -I ${OCAML_WRAPPER} -I bin/ocaml -c $@_main.ml
	ocamlopt -o $@ ${OCAML_WRAPPER}/types.cmx $@.cmx $@_main.cmx

compile-ocaml: check bin/ocaml/BinaryTrees bin/ocaml/Sieve bin/ocaml/Quicksort bin/ocaml/Fannkuch bin/ocaml/Arith

check: ast
	$(AGDA2LAMBOX) --out-dir ast --typed BinaryTrees.agda
	mv ast/BinaryTrees.ast ast/BinaryTrees_typed.ast
	$(AGDA2LAMBOX) --out-dir ast --typed Fannkuch.agda
	mv ast/Fannkuch.ast ast/Fannkuch_typed.ast
	$(AGDA2LAMBOX) --out-dir ast --typed Sieve.agda
	mv ast/Sieve.ast ast/Sieve_typed.ast
	$(AGDA2LAMBOX) --out-dir ast --typed Quicksort.agda
	mv ast/Quicksort.ast ast/Quicksort_typed.ast
	$(AGDA2LAMBOX) --out-dir ast --typed Arith.agda
	mv ast/Arith.ast ast/Arith_typed.ast
	$(AGDA2LAMBOX) --out-dir ast BinaryTrees.agda
	$(AGDA2LAMBOX) --out-dir ast Fannkuch.agda
	$(AGDA2LAMBOX) --out-dir ast Sieve.agda
	$(AGDA2LAMBOX) --out-dir ast Quicksort.agda
	$(AGDA2LAMBOX) --out-dir ast Arith.agda

clean:
	rm -rf ast/
	rm -rf bin/
