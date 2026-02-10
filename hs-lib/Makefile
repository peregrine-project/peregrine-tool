all: theory haskell-build
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile
	+@make -f RocqMakefile
	patch -p0 --forward < fix_extraction.patch || true
.PHONY: theory

haskell-build: theory
	cabal build
.PHONY: haskell-build

haskell-install: theory
	cabal install --overwrite-policy=always
.PHONY: haskell-install

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
	cabal clean
	find extraction/. -type f -name "*.hs" -delete
.PHONY: clean

clean-make:
	rm -f RocqMakefile
.PHONY: clean-make

install: RocqMakefile
	+@make -f RocqMakefile install
.PHONY: install

uninstall: RocqMakefile
	+@make -f RocqMakefile uninstall
.PHONY: uninstall
