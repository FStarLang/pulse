PULSE_HOME ?= ../../../..
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/pulse/examples
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
SRC_DIRS = common dpe engine l0
INCLUDE_PATHS += cbor
#/Pulse.Lib.HashTable.fst
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
all: verify dpe-ast

include $(PULSE_HOME)/share/pulse/Makefile.include

%.ast:
	$(FSTAR) --admit_smt_queries true --codegen Extension $(subst .ast,, $(notdir $@)) --extract_module $(basename $(subst .ast,, $(notdir $@)))

DPE_FILES = EngineTypes.fst \
  EngineCore.fst \
	L0Types.fst \
	L0Crypto.fst \
	L0Core.fst \
	Pulse.Lib.HashTable.Type.fst \
	Pulse.Lib.HashTable.Spec.fst \
	Pulse.Lib.HashTable.fst \
	DPETypes.fst \
	DPE.fst

dpe-ast: $(addsuffix .ast, $(DPE_FILES))

.PHONY: dpe-ast