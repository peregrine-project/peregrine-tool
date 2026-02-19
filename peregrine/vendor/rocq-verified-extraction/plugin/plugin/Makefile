PLUGINPATH = ../../lib/rocq_verified_extraction_plugin/_build/install/default/lib:../../lib/rocq_verified_extraction_ocaml_ffi/_build/install/default/lib

all: plugin

Makefile.rocq: _RocqProject
	coq_makefile -f _RocqProject -o Makefile.rocq

plugin: Makefile.rocq
	mkdir -p -m 0755 _build
	OCAMLPATH=${PLUGINPATH}:${OCAMLPATH} $(MAKE) -f Makefile.rocq

install: plugin
	$(MAKE) -f Makefile.rocq install
	
uninstall: Makefile.rocq
	$(MAKE) -f Makefile.rocq uninstall
	
clean: Makefile.rocq
	make -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

.merlin: Makefile.rocq
	make -f $< $@

cleanplugin: Makefile.rocq
	make -f Makefile.rocq clean
