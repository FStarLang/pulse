SUBDIRS += code

PULSE_ROOT ?= ..
include $(PULSE_ROOT)/mk/test.mk

.PHONY: sphinx
sphinx: code.__all
	sphinx-build . _build/