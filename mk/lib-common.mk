SRC := lib/common
CACHE_DIR := lib/pulse/_cache
OUTPUT_DIR := lib/pulse/_output
CODEGEN := NONE
FSTAR_OPTIONS += --include out/lib/pulse
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar'
TAG=common
include mk/boot.mk
.DEFAULT_GOAL := verify # no extraction
