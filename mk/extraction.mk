FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)
FSTAR_STAGE ?= $(FSTAR_HOME)/stage2

TAG := extraction
SRC := src/extraction
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_STAGE)/fstarc.checked
EXTRACT += --extract '-*,+ExtractPulse,+ExtractPulseC'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect
DEPFLAGS += --already_cached 'Prims,FStarC'

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk
