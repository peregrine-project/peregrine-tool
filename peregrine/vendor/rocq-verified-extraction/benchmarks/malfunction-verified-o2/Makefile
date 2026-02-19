COQOPTS = -R ../lib VerifiedExtraction.Benchmarks.lib -w -extraction-opaque-accessed,-notation-overridden,-opaque-let
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.mlf, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests mainopt run

.PHONY: run clean cleanml

$(MLFILES): tests
$(CMXFILES): $(TESTS)
exec: $(TESTS)

clean:
	rm -f ./*.cmi
	rm -f ./*.cmo
	rm -f ./*.cmx
	rm -f ./*.cma
	rm -f ./*.o
	rm -f $(TESTS)
	rm -f main mainopt
	rm -f ./*.vo ./*.vos ./*.vok

cleanml :
	rm -f $(MLFFILES) $(MLIFILES)

$(TESTS): axioms.cmx $(MLFFILES)
	@ocamlc -c $@.mli 
	@malfunction cmx -O2 $@.mlf

axioms.cmx: axioms.ml
	@ocamlopt -c axioms.ml

mainopt: $(MLFFILES) $(CMXFILES)
	@ocamlfind ocamlopt -c -thread -package core,core_bench,core_unix.command_unix main.ml
	@ocamlfind ocamlopt -linkpkg -thread -package core,core_bench,core_unix.command_unix $(CMXFILES) main.cmx -o main.native

tests: tests.v
	@coqc $(COQOPTS) tests.v > /dev/null

build: tests $(TESTS) mainopt 

run: build
	@echo "Bootstrapped Malfunction optimisations -O2"
	@./main.native +time -quota 100s -ci-absolute -clear-columns -sexp  | sexp query each | sexp to-csv | awk -F "\"*,\"*" '{print $$17","$$18","$$19}' | tail -n +2

nice: build
	@echo "Bootstrapped Malfunction optimisations -O2"
	@./main.native +time -quota 100s -ci-absolute -clear-columns

ci: build
	@echo "Bootstrapped Malfunction optimisations -O2"
	@./main.native +time -quota 1s -ci-absolute -clear-columns

.NOTPARALLEL: tests run nice ci
