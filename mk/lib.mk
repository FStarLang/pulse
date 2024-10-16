PULSE_HOME ?= $(abspath ../..)

SRC := .
CACHE_DIR := _cache
OUTPUT_DIR := _output
CODEGEN := NONE
FSTAR_OPTIONS += --include $(abspath $(PULSE_HOME)/out/lib/pulse)
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar'

all: verify-all
include $(PULSE_HOME)/mk/boot.mk
