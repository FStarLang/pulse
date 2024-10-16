FSTAR_EXE ?= $(shell which fstar.exe)

.PHONY: all
all: build
	# +$(MAKE) test

.PHONY: build
build: rustlib extract
	eval $$($(FSTAR_EXE) --ocamlenv) && cd src/ocaml && dune build
	cp -f src/_build/default/ocaml/main.exe .

.PHONY: rustlib
rustlib:
	cd src/ocaml && cargo build && cp target/debug/librustast_bindings.a ./librustast_bindings.a

.PHONY: extract
extract:
	+$(MAKE) -C src ocaml

.PHONY: test
test:
	+$(MAKE) -C tests/
