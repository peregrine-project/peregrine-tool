COQOPTS = -R ./ VerifiedExtraction.Benchmarks -R lib VerifiedExtraction.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

all: tests

.PHONY: all default clean lib cleanlib tests run copy $(TESTS)

.SILENT: lib

lib:
	@echo "Building benchmark files in Rocq"
	make -C lib > /dev/null 2>&1

cleanlib:
	$(MAKE) clean -C lib

tests: lib
	make -C ocaml-o0 all
	make -C ocaml all
	make -C ocaml-noopt all
	make -C malfunction all
	make -C malfunction-o2 all
	make -C malfunction-verified all
	make -C malfunction-verified-o2 all

ci: lib
	make -C ocaml-o0 ci
	make -C ocaml ci
	make -C ocaml-noopt ci
	make -C malfunction ci
	make -C malfunction-o2 ci
	make -C malfunction-verified ci
	make -C malfunction-verified-o2 ci

nice: lib
	make -C ocaml-o0 nice
	make -C ocaml nice
	make -C ocaml-noopt nice
	make -C malfunction nice
	make -C malfunction-o2 nice
	make -C malfunction-verified nice
	make -C malfunction-verified-o2 nice


