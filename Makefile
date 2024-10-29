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
all: install-lib # build plugin and library, and install in out/
all: lib-core    # also check impls in core
all: pulse2rust  # and pulse2rust tool

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

install-lib: plugin lib-pulse
	# Install library (cp -u: don't copy unless newer)
	rm -rf out/lib/pulse/lib
	mkdir -p out/lib/pulse/lib
	find lib/pulse lib/common \
		\( -name '*.fst' -o -name '*.fsti' -o -name '*.checked' \) \
		-exec cp -u -t out/lib/pulse/lib {} \;
	echo 'lib' > out/lib/pulse/fstar.include
	# We install share/ too (it's unclear to me why, but I'm retaining
	# it. However I am moving all tests (bug-reports, etc) out since
	# they are not interesting to users).
	rm -rf out/share
	cp -t out -r share/

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
	+$(MAKE) -C test

.PHONY: test-share
test-share: plugin lib-pulse
	+$(MAKE) -C share/pulse

.PHONY: test-pulse2rust
test-pulse2rust: test-pulse
	+$(MAKE) -C pulse2rust
	+$(MAKE) -C pulse2rust test

.PHONY: test
test: test-pulse test-share test-pulse2rust

.PHONY: pulse2rust
pulse2rust: lib-pulse plugin
	+$(MAKE) -C pulse2rust

# Make can figure out internal dependencies between all and test.
.PHONY: ci
ci: all test
