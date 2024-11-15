.PHONY: all
all: run

.PHONY: dune
dune:
	opam exec --switch=5.1.1 -- dune build --root=dune

.PHONY: run
run: dune
	./dune/_build/default/driver.exe
