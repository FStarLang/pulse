SRC := lib/pulse
CACHE_DIR := lib/pulse/_cache
OUTPUT_DIR := lib/pulse/_output
CODEGEN := NONE
FSTAR_OPTIONS += --include out/lib/pulse
FSTAR_OPTIONS += --include lib/common
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar'
TAG=pulse
include mk/boot.mk
all: verify-all
.DEFAULT_GOAL := all
