PULSE_HOME ?= ../../..
PULSE_SHARE = $(PULSE_HOME)/share/pulse

SRC_DIRS = bug-reports by-example parallel parix c .
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse/c
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

all: verify test dice

include $(PULSE_SHARE)/Makefile.include

.PHONY: dice
dice:
	+$(MAKE) -C dice

ifeq (,$(CACHE_DIRECTORY))
	extractiontest_fst_checked=ExtractionTest.fst.checked
else
	extractiontest_fst_checked=$(CACHE_DIRECTORY)/ExtractionTest.fst.checked
endif

extract: $(extractiontest_fst_checked)
#	$(FSTAR) --odir $(OUTPUT_DIRECTORY) --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --codegen OCaml ExtractionTest.fst --extract ExtractionTest

extract_c: $(extractiontest_fst_checked)
	$(FSTAR) --codegen krml ExtractionTest.fst --extract ExtractionTest
	$(KRML_HOME)/krml -bundle ExtractionTest=* -skip-compilation $(OUTPUT_DIRECTORY)/ExtractionTest.krml -tmpdir $(OUTPUT_DIRECTORY)

#	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
#	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation $(OUTPUT_DIRECTORY)/out.krml

ifneq (,$(KRML_HOME))
test-dpe-c: dice
	+$(MAKE) -C dice test-c

test-cbor: dice
	+$(MAKE) -C dice/cbor

ifeq (,$(CACHE_DIRECTORY))
	pulsepointstruct_fst_checked=c/PulsePointStruct.fst.checked
else
	pulsepointstruct_fst_checked=$(CACHE_DIRECTORY)/PulsePointStruct.fst.checked
endif

extract_pulse_c: $(pulsepointstruct_fst_checked)
	$(FSTAR) --odir $(OUTPUT_DIRECTORY) --codegen krml PulsePointStruct.fst --extract PulsePointStruct
	$(KRML_HOME)/krml -bundle PulsePointStruct=* -skip-linking $(OUTPUT_DIRECTORY)/PulsePointStruct.krml -tmpdir $(OUTPUT_DIRECTORY)

else
test-dpe-c:

test-cbor:

extract_pulse_c:

endif

test: test-cbor extract_pulse_c test-dpe-c test-error-messages

test-error-messages:
	+$(MAKE) -C bug-reports/error-messages

.PHONY: test-dpe-c test-error-messages

.PHONY: extract_pulse_c

.PHONY: test test-cbor test-cbor-raw
