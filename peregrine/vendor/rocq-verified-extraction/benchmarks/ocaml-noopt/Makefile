COQOPTS = -R ../lib VerifiedExtraction.Benchmarks.lib -w -extraction-opaque-accessed,-notation-overridden,-opaque-let
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.ml, $(TESTS))
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

$(TESTS): $(MLFFILES)
	@ocamlopt -c $@.mli
	@ocamlopt -O2 -c $@.ml

mainopt: $(MLFFILES) $(CMXFILES)
	@ocamlfind ocamlopt -c -thread -package core,core_bench,core_unix.command_unix main.ml
	@ocamlfind ocamlopt -linkpkg -thread -package core,core_bench,core_unix.command_unix $(CMXFILES) main.cmx -O2 -o main.native

tests: tests.v
	@coqc $(COQOPTS) tests.v > /dev/null

build: $(TESTS) mainopt 

run: tests mainopt
	@echo "OCaml -O2 with extraction optimisations off:"
	@./main.native +time -quota 100s -ci-absolute -clear-columns -sexp  | sexp query each | sexp to-csv | awk -F "\"*,\"*" '{print $$17","$$18","$$19}' | tail -n +2

nice: tests mainopt
	@echo "OCaml -O2 with extraction optimisations off:"
	@./main.native +time -quota 100s -ci-absolute -clear-columns

ci: tests mainopt
	@echo "OCaml -O2 with extraction optimisations off:"
	@./main.native +time -quota 1s -ci-absolute -clear-columns

.NOTPARALLEL: tests run nice ci
