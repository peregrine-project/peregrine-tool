# IO through a free monad, interpreted in Rocq (FreeIO.v).  Only the primitives
# are written per backend: ocaml/axioms.ml and c/freeio_prims.c.  On Wasm the
# host interprets the tree (wasm/host.mjs).
#   make check   builds the program for OCaml and C and runs it with input 3,
#                and wasm/WasmIO.v under the Node host wasm/host.mjs.
PEREGRINE ?= peregrine
# extra flags of the OCaml and Wasm builds, e.g. --cse true --specialize-instances true
PEREGRINE_FLAGS ?=
COQC      ?= coqc
CC        ?= gcc
NODE      ?= node
RUNTIME   ?= $(shell $(COQC) -where)/user-contrib/CertiRocq/Plugin/runtime
EXPECTED  := 3 4 result 6

# SEIO*'s own OCaml realization of its IO operations, at the revision the
# Peregrine CI checks SEIO* against
SEIO_REV  := 23d998f1b108f898f63f686ef9a596f7340cf48f
SEIO_AXIOMS := https://raw.githubusercontent.com/andricicezar/fstar-io/$(SEIO_REV)/seiostar/lambdabox/axioms.ml

all: build/ocaml/freeio build/c/freeio build/seio/ocaml/echo build/seio/c/echo build/wasm/wasmio.wasm
.PHONY: all check clean

build/FreeIO.ast: FreeIO.v
	mkdir -p build
	$(COQC) FreeIO.v

build/ocaml/freeio: build/FreeIO.ast ocaml/axioms.ml ocaml/driver.ml
	mkdir -p build/ocaml
	cp ocaml/axioms.ml ocaml/driver.ml build/ocaml/
	$(PEREGRINE) ocaml build/FreeIO.ast -o build/ocaml/FreeIO.mlf $(PEREGRINE_FLAGS)
	cd build/ocaml && echo 'val main : Obj.t' > FreeIO.mli && ocamlfind ocamlopt -c FreeIO.mli \
	  && ocamlfind ocamlopt -c axioms.ml && malfunction cmx FreeIO.mlf \
	  && ocamlfind ocamlopt -c driver.ml && ocamlfind ocamlopt -o freeio axioms.cmx FreeIO.cmx driver.cmx

build/c/freeio: build/FreeIO.ast c/config.sexp c/freeio_prims.c c/freeio_prims.h c/main.c
	mkdir -p build/c
	# the generated C includes its header by the path given to -o
	cd build/c && $(PEREGRINE) compile ../FreeIO.ast ../../c/config.sexp -o freeio.c
	$(CC) -O2 -I$(RUNTIME) -Ic -Ibuild/c -o $@ build/c/freeio.c c/freeio_prims.c c/main.c \
	  $(RUNTIME)/gc_stack.c $(RUNTIME)/prim_int63.c

build/Echo.ast: seio/Runtime.v seio/Echo.v
	mkdir -p build
	cd seio && $(COQC) -Q . "" Runtime.v && $(COQC) -Q . "" Echo.v

build/seio/ocaml/echo: build/Echo.ast seio/driver.ml
	mkdir -p build/seio/ocaml
	curl -sSfL --retry 5 $(SEIO_AXIOMS) -o build/seio/ocaml/axioms.ml
	cp seio/driver.ml build/seio/ocaml/
	$(PEREGRINE) ocaml build/Echo.ast -o build/seio/ocaml/Echo.mlf $(PEREGRINE_FLAGS)
	cd build/seio/ocaml && echo 'val main : Obj.t' > Echo.mli && ocamlfind ocamlopt -c Echo.mli \
	  && ocamlfind ocamlopt -package unix -c axioms.ml && malfunction cmx Echo.mlf \
	  && ocamlfind ocamlopt -c driver.ml && ocamlfind ocamlopt -package unix -linkpkg -o echo axioms.cmx Echo.cmx driver.cmx

build/seio/c/echo: build/Echo.ast seio/config.sexp seio/runtime_prims.c seio/runtime_prims.h seio/main.c
	mkdir -p build/seio/c
	cd build/seio/c && $(PEREGRINE) compile ../../Echo.ast ../../../seio/config.sexp -o echo.c
	$(CC) -O2 -I$(RUNTIME) -Iseio -Ibuild/seio/c -o $@ build/seio/c/echo.c seio/runtime_prims.c seio/main.c \
	  $(RUNTIME)/gc_stack.c $(RUNTIME)/prim_int63.c $(RUNTIME)/prim_string.c

# The Wasm module has no imports: the host performs the operations of the
# free-monad tree that the program returns (wasm/host.mjs).
build/WasmIO.ast: wasm/WasmIO.v
	mkdir -p build
	cd wasm && $(COQC) -Q . "" WasmIO.v

build/wasm/wasmio.wasm: build/WasmIO.ast
	mkdir -p build/wasm
	$(PEREGRINE) wasm build/WasmIO.ast -o $@ $(PEREGRINE_FLAGS)

check: all
	@for b in ocaml c; do \
	  got=$$(echo hello | build/seio/$$b/echo | tr '\n' ' ' | sed 's/ $$//'); \
	  if [ "$$got" = "hello hello" ]; then echo "ok   seio $$b: $$got"; \
	  else echo "FAIL seio $$b: got '$$got', expected 'hello hello'"; exit 1; fi; \
	done
	@for b in ocaml c; do \
	  got=$$(echo 3 | build/$$b/freeio | tr '\n' ' ' | sed 's/ $$//'); \
	  if [ "$$got" = "$(EXPECTED)" ]; then echo "ok   $$b: $$got"; \
	  else echo "FAIL $$b: got '$$got', expected '$(EXPECTED)'"; exit 1; fi; \
	done
	@got=$$(echo 3 | $(NODE) wasm/host.mjs build/wasm/wasmio.wasm | tr '\n' ' ' | sed 's/ $$//'); \
	if [ "$$got" = "$(EXPECTED)" ]; then echo "ok   wasm: $$got"; \
	else echo "FAIL wasm: got '$$got', expected '$(EXPECTED)'"; exit 1; fi

clean:
	rm -rf build *.vo *.vok *.vos *.glob .*.aux seio/*.vo seio/*.vok seio/*.vos seio/*.glob seio/.*.aux \
	  wasm/*.vo wasm/*.vok wasm/*.vos wasm/*.glob wasm/.*.aux
