all: build
.PHONY: all

build: theory mllib plugin
.PHONY: build

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

plugin: theory
	+@make -C plugin
.PHONY: plugin

test:
	+@make -C test test
.PHONY: test

mllib: theory
	dune build
.PHONY: mllib

hs-lib: theory
	+@make -C hs-lib
.PHONY: hs-lib

clean-extraction:
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete

clean: RocqMakefile
	+@make -f RocqMakefile clean
	+@make -C plugin clean
	rm -f RocqMakefile
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete
.PHONY: clean

install: build
	dune install
	+@make -f RocqMakefile install
	+@make -C plugin install
.PHONY: install

uninstall:
	dune uninstall
	+@make -f RocqMakefile uninstall
	+@make -C plugin uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: RocqMakefile force
	+@make -f RocqMakefile $@
force: ;
all: theory

# Do not forward these files
Makefile _CoqProject: ;
