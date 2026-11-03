# IO through a free monad, interpreted in Rocq (FreeIO.v).  Only the primitives
# are written per backend: ocaml/axioms.ml and c/freeio_prims.c.
#   make check   builds the program for OCaml and C and runs it with input 3.
PEREGRINE ?= peregrine
COQC      ?= coqc
CC        ?= gcc
RUNTIME   ?= $(shell $(COQC) -where)/user-contrib/CertiRocq/Plugin/runtime
EXPECTED  := 3 4 result 6

all: build/ocaml/freeio build/c/freeio
.PHONY: all check clean

build/FreeIO.ast: FreeIO.v
	mkdir -p build
	$(COQC) FreeIO.v

build/ocaml/freeio: build/FreeIO.ast ocaml/axioms.ml ocaml/driver.ml
	mkdir -p build/ocaml
	cp ocaml/axioms.ml ocaml/driver.ml build/ocaml/
	$(PEREGRINE) ocaml build/FreeIO.ast -o build/ocaml/FreeIO.mlf
	cd build/ocaml && echo 'val main : Obj.t' > FreeIO.mli && ocamlfind ocamlopt -c FreeIO.mli \
	  && ocamlfind ocamlopt -c axioms.ml && malfunction cmx FreeIO.mlf \
	  && ocamlfind ocamlopt -c driver.ml && ocamlfind ocamlopt -o freeio axioms.cmx FreeIO.cmx driver.cmx

build/c/freeio: build/FreeIO.ast c/config.sexp c/freeio_prims.c c/freeio_prims.h c/main.c
	mkdir -p build/c
	# the generated C includes its header by the path given to -o
	cd build/c && $(PEREGRINE) compile ../FreeIO.ast ../../c/config.sexp -o freeio.c
	$(CC) -O2 -I$(RUNTIME) -Ic -Ibuild/c -o $@ build/c/freeio.c c/freeio_prims.c c/main.c \
	  $(RUNTIME)/gc_stack.c $(RUNTIME)/prim_int63.c

check: all
	@for b in ocaml c; do \
	  got=$$(echo 3 | build/$$b/freeio | tr '\n' ' ' | sed 's/ $$//'); \
	  if [ "$$got" = "$(EXPECTED)" ]; then echo "ok   $$b: $$got"; \
	  else echo "FAIL $$b: got '$$got', expected '$(EXPECTED)'"; exit 1; fi; \
	done

clean:
	rm -rf build FreeIO.vo FreeIO.vok FreeIO.vos FreeIO.glob .FreeIO.aux
