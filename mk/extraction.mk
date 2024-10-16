FSTAR_EXE   ?= $(shell which fstar.exe)
FSTAR_STAGE ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../..)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)

CACHE_DIR := build/extraction.checked
OUTPUT_DIR := build/extraction.ml
SRC := src/extraction
CODEGEN := PluginNoLib
TAG := extraction
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_STAGE)/fstarc.checked
# FSTAR_OPTIONS += --include $(FSTAR_STAGE)/plugins.checked
# FSTAR_OPTIONS += --include $(FSTAR_STAGE)/ulib.checked
EXTRACT += --extract '-*,+ExtractPulse,+ExtractPulseC'
include mk/boot-lax.mk
