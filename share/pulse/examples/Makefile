PULSE_HOME ?= ../../..
PULSE_SHARE = $(PULSE_HOME)/share/pulse

SRC_DIRS = bug-reports by-example parallel parix c .
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse/c
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

.PHONY: all
all: verify test dice

include $(PULSE_SHARE)/Makefile.include

.PHONY: dice
dice:
	+$(MAKE) -C dice

EXTRA_KRML_OPTS=-skip-linking

$(OUTPUT_DIRECTORY)/%.c: $(OUTPUT_DIRECTORY)/%.krml
	$(KRML_HOME)/krml -bundle $*=* $(EXTRA_KRML_OPTS) $< -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
extract: $(OUTPUT_DIRECTORY)/ExtractionTest.ml

.PHONY: extract_c
extract_c: $(OUTPUT_DIRECTORY)/ExtractionTest.c

.PHONY: extract_pulse_c
extract_pulse_c: $(OUTPUT_DIRECTORY)/PulsePointStruct.c

.PHONY: test-cbor
test-cbor: dice
	+$(MAKE) -C dice/cbor

.PHONY: test
ifeq (,$(KRML_HOME))
test: extract
else
test: extract test-cbor extract_c extract_pulse_c
endif
