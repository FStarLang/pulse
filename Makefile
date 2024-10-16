include mk/common.mk

# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.
# GM: ifeq? That sounds oddly specific?
# Also is this still true?
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

.DEFAULT_GOAL := all
all: plugin lib core

.PHONY: .force
.force:

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(CURDIR))
else
  PULSE_HOME := $(CURDIR)
endif

FSTAR_EXE ?= $(shell which fstar.exe)
ifeq ($(FSTAR_EXE),)
_ := $(error I need F*: please put it in your PATH or set FSTAR_EXE)
endif

plugin: plugin.src .force
	$(FSTAR_EXE) --ocamlenv \
	  dune build --root=build/ocaml
	mkdir -p out
	$(FSTAR_EXE) --ocamlenv \
	  dune install --root=build/ocaml --prefix=$(abspath out)

plugin.src: checker.src extraction.src syntax_extension.src

checker.src: .force
	$(MAKE) -f mk/checker.mk
	
extraction.src: .force
	$(MAKE) -f mk/extraction.mk

syntax_extension.src: .force
	$(MAKE) -f mk/syntax_extension.mk

lib-pulse: plugin lib-common .force
	$(MAKE) -f mk/lib-pulse.mk

lib-core: lib-common .force
	$(MAKE) -f mk/lib-core.mk

lib-common: .force
	$(MAKE) -f mk/lib-common.mk

clean:
	$(MAKE) -f mk/checker.mk clean
	$(MAKE) -f mk/extraction.mk clean
	$(MAKE) -f mk/syntax_extension.mk clean
	$(MAKE) -C lib/pulse clean

.PHONY: test
test: plugin lib
	+$(MAKE) -C share/pulse

.PHONY: pulse2rust
pulse2rust: lib plugin
	+$(MAKE) -C pulse2rust
