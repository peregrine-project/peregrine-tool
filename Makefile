all: build
.PHONY: all

build: theory mllib
.PHONY: build

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

test:
	+@make -C test test
.PHONY: test

mllib: theory
	dune build
.PHONY: mllib

clean-extraction:
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete
.PHONY: clean

install: build
	dune install
.PHONY: install

uninstall:
	dune uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: RocqMakefile force
	+@make -f RocqMakefile $@
force: ;
all: theory

# Do not forward these files
Makefile _CoqProject: ;
