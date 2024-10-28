include mk/common.mk
include mk/locate.mk

# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.
# GM: ifeq? That sounds oddly specific?
# Also is this still true?
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

.DEFAULT_GOAL := all
all: plugin lib-pulse lib-core pulse2rust

.PHONY: .force
.force:

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
	$(MAKE) -f mk/lib-pulse.mk clean
	$(MAKE) -f mk/lib-core.mk clean
	$(MAKE) -f mk/lib-common.mk clean

.PHONY: test-pulse
test-pulse: plugin lib-pulse
	+$(MAKE) -C share/pulse

.PHONY: test-pulse2rust
test-pulse2rust: test-pulse
	+$(MAKE) -C pulse2rust
	+$(MAKE) -C pulse2rust test

.PHONY: test
test: test-pulse test-pulse2rust

.PHONY: pulse2rust
pulse2rust: lib-pulse plugin
	+$(MAKE) -C pulse2rust

# Make can figure out internal dependencies between all and test.
.PHONY: ci
ci: all test
