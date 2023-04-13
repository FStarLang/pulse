all: lib verify

# Regeneration rules

.PHONY: extract-ocaml
extract-ocaml: extract-tactics extract-extraction

.PHONY: extract-tactics
extract-tactics:
	+$(MAKE) -C src/ocaml -f extract-tactics.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C src/extraction

.PHONY: extract-c
extract-c: verify
	+$(MAKE) verify
	+$(MAKE) -C src/c extract

.PHONY: extract
extract:
	+$(MAKE) extract-ocaml
	+$(MAKE) extract-c

.PHONY: boot
boot:
	+$(MAKE) extract
	+$(MAKE) all

.PHONY: full-boot
full-boot:
	rm -rf src/ocaml/generated include/steel/Steel_SpinLock.h
	+$(MAKE) boot

# End user rules

ifneq (,$(FSTAR_HOME))
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
  export OCAMLPATH
endif

ifeq ($(OS),Windows_NT)
  STEEL_HOME := $(shell cygpath -m $(CURDIR))
else
  STEEL_HOME := $(CURDIR)
endif

.PHONY: ocaml
ocaml:
	cd src/ocaml && dune build
	cd src/ocaml && dune install --prefix=$(STEEL_HOME)

.PHONY: lib
lib:
	+$(MAKE) -C src/c

.PHONY: verify
verify: ocaml
	+$(MAKE) -C lib/steel

clean:
	+$(MAKE) -C lib/steel clean ; true
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel
