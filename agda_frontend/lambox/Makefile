all: build
.PHONY: all

build:
	cabal build
.PHONY: haskell-build

install:
	cabal install --overwrite-policy=always
.PHONY: haskell-install

clean: RocqMakefile
	cabal clean
.PHONY: clean
