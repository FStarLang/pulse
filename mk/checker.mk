CACHE_DIR := build/src.checked
OUTPUT_DIR := build/src.ml
SRC := src/checker/
CODEGEN := PluginNoLib
TAG := checker
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
include mk/boot.mk
