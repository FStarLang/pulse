FSTAR_EXE   ?= $(shell which fstar.exe)
FSTAR_STAGE ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../..)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)

SRC := .

OUTPUT_DIR := $(CURDIR)/../ocaml/plugin/generated
ADDITIONAL_INCLUDES += $(FSTAR_STAGE)/fstarc.checked
ADDITIONAL_INCLUDES += $(FSTAR_STAGE)/plugins.checked
ADDITIONAL_INCLUDES += $(FSTAR_HOME)/src

FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --MLish --MLish_effect FStarC.Compiler.Effect
FSTAR_OPTIONS += --no_location_info
FSTAR_OPTIONS += --warn_error -271-272-241-319-274
FSTAR_OPTIONS += $(addprefix --include , $(ADDITIONAL_INCLUDES))
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --already_cached 'Prims,FStar'
FSTAR_OPTIONS += --warn_error -321

EXTRACT = --extract 'ExtractPulse,ExtractPulseC'

CACHE_DIR = _cache

CODEGEN := PluginNoLib

TAG := extraction

ROOTS = $(wildcard *.fst *.fsti)

include ../../mk/boot.mk

.DEFAULT_GOAL := ocaml
