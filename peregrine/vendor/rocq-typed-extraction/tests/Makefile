all: tests
.PHONY: all

_CoqProject: _CoqProject.in _config
	cat _config > _CoqProject
	cat _CoqProject.in >> _CoqProject

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

tests: theory process-extraction-examples
.PHONY: tests

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

process-extraction-examples: theory
	./process-extraction-examples.sh
.PHONY: process-extraction-examples



# Rust tests

RUST_DIR=./extracted-code/rust

test-rust-extraction: clean-rust-compiled-extraction
	$(foreach dir, $(wildcard $(RUST_DIR)/*-extracted), cd $(dir) && cargo run && cd ../../../;)
.PHONY: test-rust-extraction

clean-rust-compiled-extraction:
	$(foreach dir, $(wildcard $(RUST_DIR)/*-extracted), rm -f -r $(dir)/target;)
.PHONY: clean-rust-compiled-extraction

clean-rust-extraction-out-files:
	rm -f $(RUST_DIR)/*.rs.out
.PHONY: clean-rust-extraction-out-files

clean-rust-extraction-sources:
	find $(RUST_DIR) -name 'main.rs' -delete
.PHONY:clean-extraction-sources

clean-rust-extraction: clean-rust-compiled-extraction clean-rust-extraction-out-files clean-rust-extraction-sources
.PHONY: clean-rust-extraction



# Elm tests

ELM_DIR=./extracted-code/elm/elm-extract
ELM_WEB_APP_DIR=./extracted-code/elm/elm-web-extract

test-elm-extraction: clean-elm-compiled-extraction
	mkdir -p $(ELM_DIR)/src
	cd $(ELM_DIR); elm-test
	cd $(ELM_WEB_APP_DIR); elm make src/Main.elm
.PHONY: test-elm-extraction

clean-elm-compiled-extraction:
	rm -f -r $(ELM_WEB_APP_DIR)/elm-stuff
	rm -f -r $(ELM_WEB_APP_DIR)/index.html
	rm -f -r $(ELM_DIR)/elm-stuff
.PHONY: clean-elm-compiled-extraction

clean-elm-extraction-out-files:
	rm -f $(ELM_WEB_APP_DIR)/*.elm.out
	rm -f $(ELM_DIR)/*.elm.out
.PHONY: clean-elm-extraction-out-files

clean-elm-extraction-sources:
	rm -f $(ELM_DIR)/tests/*.elm
	rm -f $(ELM_WEB_APP_DIR)/src/main.elm
.PHONY: clean-elm-extraction-sources

clean-elm-extraction: clean-elm-compiled-extraction clean-elm-extraction-out-files clean-elm-extraction-sources
.PHONY: clean-elm-extraction



# Tests

test-extraction: test-rust-extraction test-elm-extraction
.PHONY: test-extraction

clean-extraction-examples:
	rm ./thories/*.vo # to force recompilation of examples (a bit ad-hoc though)
.PHONY: clean-extraction-examples

clean-extraction: clean-extraction-examples clean-rust-extraction clean-elm-extraction
.PHONY: clean-extraction
