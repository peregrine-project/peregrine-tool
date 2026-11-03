# Tasks (Tasks.v): spawn and get are realized as OCaml threads and as Lean's Task.
#   make check         builds the program for OCaml and Lean and runs it
#   make check-ocaml   OCaml only, without Lean
PEREGRINE ?= peregrine
COQC      ?= coqc
LAKE      ?= lake
EXPECTED  := 17711
ROOT      := $(abspath ../..)

all: build/ocaml/tasks build/lean/tasks
.PHONY: all check check-ocaml clean

build/Tasks.ast: Tasks.v
	mkdir -p build
	$(COQC) Tasks.v

build/ocaml/tasks: build/Tasks.ast ocaml/axioms.ml ocaml/driver.ml
	mkdir -p build/ocaml
	cp ocaml/axioms.ml ocaml/driver.ml build/ocaml/
	$(PEREGRINE) ocaml build/Tasks.ast -o build/ocaml/Tasks.mlf
	cd build/ocaml && echo 'val main : Obj.t' > Tasks.mli && ocamlfind ocamlopt -c Tasks.mli \
	  && ocamlfind ocamlopt -package threads.posix -thread -c axioms.ml && malfunction cmx Tasks.mlf \
	  && ocamlfind ocamlopt -c driver.ml \
	  && ocamlfind ocamlopt -package threads.posix -thread -linkpkg -o tasks axioms.cmx Tasks.cmx driver.cmx

# A Lake project with the Lean backend's runtime, the generated module and a main.
build/lean/tasks: build/Tasks.ast lean/remap.sexp lean/Main.lean lean/lakefile.toml
	mkdir -p build/lean/Peregrine
	cp lean/Main.lean lean/lakefile.toml build/lean/
	cp $(ROOT)/lean-toolchain build/lean/
	cp $(ROOT)/lean/Peregrine/Runtime.lean build/lean/Peregrine/
	$(PEREGRINE) compile build/Tasks.ast lean/remap.sexp -o build/lean/Gen.lean
	cd build/lean && $(LAKE) build tasks && cp .lake/build/bin/tasks tasks

check: all
	@for b in ocaml lean; do \
	  got=$$(build/$$b/tasks); \
	  if [ "$$got" = "$(EXPECTED)" ]; then echo "ok   $$b: $$got"; \
	  else echo "FAIL $$b: got '$$got', expected '$(EXPECTED)'"; exit 1; fi; \
	done

check-ocaml: build/ocaml/tasks
	@got=$$(build/ocaml/tasks); \
	if [ "$$got" = "$(EXPECTED)" ]; then echo "ok   ocaml: $$got"; \
	else echo "FAIL ocaml: got '$$got', expected '$(EXPECTED)'"; exit 1; fi

clean:
	rm -rf build *.vo *.vok *.vos *.glob .*.aux
