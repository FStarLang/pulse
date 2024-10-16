FSTAR_EXE   ?= $(shell which fstar.exe)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)
FSTAR_STAGE ?= $(FSTAR_HOME)/stage2

TAG := pulse2rust
SRC := .
CACHE_DIR := _cache
OUTPUT_DIR := ocaml/generated
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_STAGE)/fstarc.checked
EXTRACT += --extract '-*,+Pulse2Rust'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect
DEPFLAGS += --already_cached 'Prims,FStarC'

PULSE_ROOT ?= ../..
include $(PULSE_ROOT)/mk/boot.mk
