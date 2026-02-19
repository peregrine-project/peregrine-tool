all: Makefile.rocq
	mkdir -p -m 0755 _build
	make -f Makefile.rocq

_RocqProject: 
	git ls-files > _RocqProject

Makefile.rocq: _RocqProject
	coq_makefile -f _RocqProject -o Makefile.rocq

.PHONY: _RocqProject
