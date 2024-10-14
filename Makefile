# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

all: plugin lib

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(CURDIR))
else
  PULSE_HOME := $(CURDIR)
endif

include $(PULSE_HOME)/share/pulse/Makefile.locate-fstar

.PHONY: plugin
plugin:
	+$(MAKE) -C src build

# Note: this includes pulsecore which
# 1- Is wasteful if we just wanna get going with some Pulse code
# 2- Does not depend on the plugin
.PHONY: lib
lib: plugin
	+$(MAKE) -C lib/pulse

clean:
	+$(MAKE) -C lib/pulse clean ; true

.PHONY: test
test: plugin lib
	+$(MAKE) -C share/pulse

ifeq (,$(PREFIX))
  PREFIX := /usr/local
endif
ifeq ($(OS),Windows_NT)
  PREFIX := $(shell cygpath -m $(PREFIX))
endif
export PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-lib install-share

install-lib:
	+$(MAKE) -C lib/pulse install

install-share:
	+$(MAKE) -C share/pulse install

install: install-lib install-share

.PHONY: pulse2rust
pulse2rust: lib plugin
	+$(MAKE) -C pulse2rust

.PHONY: ci
ci:
	+$(MAKE) -C src ci
