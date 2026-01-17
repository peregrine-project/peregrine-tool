RUNTIME_PATH := $(shell `coqc -where`/user-contrib/CertiCoq/Plugin/runtime/)

all:

%.wasm: %.ast
	dune exec peregrine -- wasm -o $@ $*.ast

%.cwasm: %.wasm
	wasmtime compile $*.wasm

%.c: %.ast
	dune exec peregrine -- c -o $@ $*.ast

%.o: %.c
	gcc -o $@ -w -Wno-everything -O2 -fomit-frame-pointer -I${RUNTIME_PATH} main.c ${RUNTIME_PATH}/gc_stack.c $*.c

%.elm: %.tast
	dune exec peregrine -- elm -o $@ $*.tast

%.js: %.elm
	elm make $*.elm --output=$@

%.rs: %.tast
	dune exec peregrine -- rust -o $@ $*.tast

%.exe: %.rs
	rustc $*.rs -o $@

%.mlf: %.ast
	dune exec peregrine -- ocaml -o $@ $*.ast

%.cmx: %.mlf
	malfunction cmx $*.mlf

%.cmo: %.mlf
	malfunction cmo $*.mlf

#%.: %.mlf
#	malfunction compile $*.mlf

clean:
	find . -type f -name "*.wasm" -delete
	find . -type f -name "*.cwasm" -delete
	find . -type f -name "*.c" -delete
	find . -type f -name "*.h" -delete
	find . -type f -name "*.o" -delete
	find . -type f -name "*.elm" -delete
	find . -type f -name "*.js" -delete
	find . -type f -name "*.rs" -delete
	find . -type f -name "*.exe" -delete
	find . -type f -name "*.mlf" -delete
	find . -type f -name "*.cmx" -delete
	find . -type f -name "*.cmo" -delete
.PHONY: clean

node_modules: package.json
	npm i

test: node_modules
	npm run test
.PHONY: test
