SUBDIRS += code

PULSE_ROOT ?= ..
include $(PULSE_ROOT)/mk/test.mk

.PHONY: sphinx
sphinx:
	sphinx-build . _build/