all:
	cp ../../add.mlf test_add.mlf
	ocamlc -opaque -c test_add.mli
	malfunction cmx test_add.mlf
	ocamlopt test_add.cmx main.ml -o main
	ocamlopt test_add.cmx main.ml -o main
	./main
