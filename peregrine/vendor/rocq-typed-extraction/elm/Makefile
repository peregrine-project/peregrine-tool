all: theory
.PHONY: all

_CoqProject: _CoqProject.in _config
	cat _config > _CoqProject
	cat _CoqProject.in >> _CoqProject

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

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

# Forward most things to Rocq makefile. Use 'force' to make this phony.
%: RocqMakefile force
	+@make -f RocqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject.in _config: ;
