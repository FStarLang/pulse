CACHE_DIR := build/src.checked
OUTPUT_DIR := build/src.ml
SRC := src/checker/
CODEGEN := PluginNoLib
TAG := checker
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --already_cached 'Prims,FStar'
EXTRACT += --extract '-*,+Pulse,+PulseSyntaxExtension'
include mk/boot.mk
