# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

# ifeq? That sounds oddly specific?
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

all: plugin lib

include mk/common.mk
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

.PHONY: plugin
plugin: plugin.src
	dune --root ....

.PHONY: plugin.src
plugin.src: checker.src extraction.src syntax_extension.src

.PHONY: checker.src
checker.src:
	$(MAKE) -f mk/checker.mk
	
.PHONY: extraction.src
extraction.src:
	$(MAKE) -f mk/extraction.mk

.PHONY: syntax_extension.src
syntax_extension.src:
	$(MAKE) -f mk/syntax_extension.mk

# Note: this includes pulsecore which
# 1- Is wasteful if we just wanna get going with some Pulse code
# 2- Does not depend on the plugin
.PHONY: lib
lib: plugin
	$(MAKE) -C lib/pulse

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
