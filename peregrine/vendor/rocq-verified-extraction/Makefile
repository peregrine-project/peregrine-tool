ifeq (3.82,$(firstword $(sort $(MAKE_VERSION) 3.82)))
  # stuff that requires make-3.82 or higher
  undefine COQPATH
endif
ifeq ($(out),)
else
	PREFIX=$(out)
	INSTALLOPT=--prefix=${PREFIX} --libdir ${OCAMLFIND_DESTDIR}
endif

all: rocq extraction_plugin extraction_ocaml_ffi plugin bootstrap

extraction_ocaml_ffi:
	cd lib/rocq_verified_extraction_ocaml_ffi && dune build

extraction_plugin:
	cd lib/rocq_verified_extraction_plugin && dune build

rocq: Makefile.rocq
	+make -f Makefile.rocq all

install: install-rocq plugin

install-rocq: Makefile.rocq rocq
	+$(MAKE) -f Makefile.rocq install
	cd lib/rocq_verified_extraction_ocaml_ffi && dune install ${INSTALLOPT}
	cd lib/rocq_verified_extraction_plugin && dune install ${INSTALLOPT}
	cd plugin/plugin && $(MAKE) -f Makefile.rocq install
	cd plugin/plugin-bootstrap && $(MAKE) -f Makefile.rocq install

clean: Makefile.rocq plugin/plugin/Makefile.rocq plugin/plugin-bootstrap/Makefile.rocq
	+make -f Makefile.rocq clean
	rm -f Makefile.rocq
	rm -f Makefile.rocq.conf
	cd lib/rocq_verified_extraction_ocaml_ffi && dune clean
	cd lib/rocq_verified_extraction_plugin && dune clean
	cd plugin/plugin && make clean
	cd plugin/plugin-bootstrap && make clean

plugin/plugin/Makefile.rocq: plugin/plugin/_RocqProject
	cd plugin/plugin && make Makefile.rocq

plugin: rocq plugin/plugin/Makefile.rocq extraction_plugin extraction_ocaml_ffi
	cd plugin/plugin && ./clean_extraction.sh
	+make -C plugin/plugin

test: 
	cd plugin/tests && make 

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

plugin/plugin-bootstrap/Makefile.rocq: plugin/plugin-bootstrap/_RocqProject
	cd plugin/plugin-bootstrap && make Makefile.rocq

bootstrap: rocq plugin extraction_plugin extraction_ocaml_ffi
	+make -C plugin/plugin-bootstrap -j 1

.PHONY: extraction_plugin extraction_ocaml_ffi

html:
	rocq doc --multi-index -toc -utf8 -html \
    --with-header ./html/resources/header.html --with-footer ./html/resources/footer.html \
		--coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
		--external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
		--external https://metarocq.github.io/v1.4-9.0/ MetaRocq \
		-Q theories Malfunction \
		-Q plugin/plugin-bootstrap VerifiedExtraction \
		-Q benchmarks/lib VerifiedExtraction.Benchmarks \
		-Q examples Malfunction.Examples \
		-d html theories/*.v examples/**/*.v plugin/plugin-bootstrap/*.v benchmarks/lib/*.v
	# Overwritten by rocq doc
	git checkout html/coqdoc.css

.PHONY: html