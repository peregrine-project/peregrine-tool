all: common elm rust plugin tests
.PHONY: all

common:
	+make -C common
.PHONY: common

elm:
	+make -C elm
.PHONY: elm

rust:
	+make -C rust
.PHONY: rust

plugin:
	+make -C plugin
.PHONY: plugin

tests:
	+make -C tests
.PHONY: tests

clean:
	+make -C common clean
	+make -C elm clean
	+make -C rust clean
	+make -C plugin clean
	+make -C tests clean
	rm -rf docs
.PHONY: clean

clean-make:
	+make -C common clean-make
	+make -C elm clean-make
	+make -C rust clean-make
	+make -C plugin clean-make
	+make -C tests clean-make
.PHONY: clean-make

install: all
	+make -C common install
	+make -C elm install
	+make -C rust install
	+make -C plugin install
.PHONY: install

uninstall:
	+make -C common uninstall
	+make -C elm uninstall
	+make -C rust uninstall
	+make -C plugin uninstall
.PHONY: uninstall

html: all
	rm -rf docs
	mkdir docs
	rocq doc --html --interpolate --parse-comments \
		--with-header doc/header.html --with-footer doc/footer.html \
		--toc \
		--coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
    	--external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
		--external https://metarocq.github.io/html MetaRocq \
		-R common/theories TypedExtraction.Common \
		-R elm/theories TypedExtraction.Elm \
		-R rust/theories TypedExtraction.Rust \
		-R plugin/theories TypedExtraction.Plugin \
		-R tests/theories TypedExtraction.Tests \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*test/*" \) -name "*.v" ! -wholename "./_opam/*"`
	cp doc/resources/coqdocjs/*.js docs
	cp doc/resources/coqdocjs/*.css docs
	cp doc/resources/toc/*.js docs
	cp doc/resources/toc/*.css docs
.PHONY: html
