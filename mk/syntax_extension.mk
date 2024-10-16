FSTAR_EXE   ?= $(shell which fstar.exe)
FSTAR_STAGE ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../..)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)

CACHE_DIR := build/syntax_extension.checked
OUTPUT_DIR := build/syntax_extension.ml
SRC := src/syntax_extension
CODEGEN := PluginNoLib
TAG := syntax_extension
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_STAGE)/fstarc.checked
# FSTAR_OPTIONS += --include $(FSTAR_STAGE)/plugins.checked
# FSTAR_OPTIONS += --include $(FSTAR_STAGE)/ulib.checked
EXTRACT += --extract '-*,+PulseSyntaxExtension'
include mk/boot-lax.mk
