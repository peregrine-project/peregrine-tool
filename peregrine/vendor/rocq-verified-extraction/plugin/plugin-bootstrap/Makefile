PLUGINPATH = ../../lib/rocq_verified_extraction_plugin/_build/install/default/lib:../../lib/rocq_verified_extraction_ocaml_ffi/_build/install/default/lib

all: Makefile.bootstrap Makefile.rocq plugin
	
compile_malfunction:
	mkdir -p _build
	OCAMLPATH=${PLUGINPATH}:${OCAMLPATH} make -f Makefile.bootstrap
	cp _build/compile_malfunction.mlf compile_malfunction.mlf
	
plugin: compile_malfunction
	OCAMLPATH=${PLUGINPATH}:${OCAMLPATH} make -f Makefile.rocq

install: Makefile.rocq all
	make -f Makefile.rocq install

Makefile.bootstrap: _BootstrapProject
	coq_makefile -f _BootstrapProject -o Makefile.bootstrap

Makefile.rocq: _RocqProject
	coq_makefile -f _RocqProject -o Makefile.rocq

clean: Makefile.rocq Makefile.bootstrap
	make -f Makefile.bootstrap clean
	make -f Makefile.rocq clean
	rm -rf _build