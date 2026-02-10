all: theory
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

RocqMakefile.ci: _CoqProject.ci
	rocq makefile -f _CoqProject.ci -o RocqMakefile.ci

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

build-ci: RocqMakefile.ci
	+@make -f RocqMakefile.ci
.PHONY: build-ci

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
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
