.PHONY: all clean gen-ast compile-ast bench-c

gen-ast:
	make -C agda check
	make -C lean check
	make -C rocq check

compile-c:
	make -C agda compile-c
	make -C lean compile-c
	make -C rocq compile-c

compile-ocaml-wrapper:
	ocamlopt -c ocaml_wrapper/types.mli
	ocamlopt -I ocaml_wrapper -c ocaml_wrapper/types.ml

compile-ocaml: compile-ocaml-wrapper
	make -C agda compile-ocaml
	make -C lean compile-ocaml
	make -C rocq compile-ocaml

bench-c:
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 15\
		-L frontend agda,rocq,lean\
		-L bench BinaryTrees\
		-L backend c\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 2000\
		-L frontend agda,rocq,lean\
		-L bench Sieve\
		-L backend c\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 20\
		-L frontend agda,rocq,lean\
		-L bench Quicksort\
		-L backend c\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 9\
		-L frontend rocq,lean\
		-L bench Fannkuch\
		-L backend c\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 8\
		-L frontend agda,rocq,lean\
		-L bench Arith\
		-L backend c\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json

bench-ocaml:
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 15\
		-L frontend agda,rocq,lean\
		-L bench BinaryTrees\
		-L backend ocaml\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 2000\
		-L frontend agda,rocq,lean\
		-L bench Sieve\
		-L backend ocaml\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 20\
		-L frontend agda,rocq,lean\
		-L bench Quicksort\
		-L backend ocaml\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 9\
		-L frontend rocq,lean\
		-L bench Fannkuch\
		-L backend ocaml\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json
	hyperfine -N --warmup 3 --min-runs 10\
		-L n 8\
		-L frontend agda,rocq,lean\
		-L bench Arith\
		-L backend ocaml\
		"{frontend}/bin/{backend}/{bench} {n}"\
		--export-json results/$(shell date +"%Y-%m-%dT%T").json


clean:
	make -C agda clean
	make -C lean clean
	make -C rocq clean
