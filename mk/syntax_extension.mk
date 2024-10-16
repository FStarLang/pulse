FSTAR_STAGE ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../..)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)

TAG := syntax_extension
SRC := src/syntax_extension
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_STAGE)/fstarc.checked
EXTRACT += --extract '-*,+PulseSyntaxExtension'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect

include mk/boot.mk
