PULSE_HOME ?= ../../..

all: verify

FSTAR_OPTIONS += --already_cached '*,-PulseCore'

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    FSTAR_HOME := $(realpath $(dir $(_check_fstar))/..)
  else
    $(error "FSTAR_HOME is not defined and I cannot find fstar.exe in $(PATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
  endif
endif
ifeq ($(OS),Windows_NT)
  FSTAR_HOME := $(shell cygpath -m $(FSTAR_HOME))
endif
export FSTAR_HOME
ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif

# List the directories of all root files
SRC_DIRS += .

# List additional include paths
INCLUDE_PATHS += $(SRC_DIRS)

# Use hints by default, can be overriden
HINTS_ENABLED?=n

ifeq ($(HINTS_ENABLED),y)
USE_HINTS:=--use_hints
else
USE_HINTS:=
endif

FSTAR_OPTIONS += $(USE_HINTS)

# A place to put all build artifacts
ifneq (,$(OUTPUT_DIRECTORY))
  FSTAR_OPTIONS += --odir $(OUTPUT_DIRECTORY)
endif

# A place to put .checked files. If this variable is left empty, then
# each .checked file will be generated right next to its corresponding
# source file.
ifneq (,$(CACHE_DIRECTORY))
  FSTAR_OPTIONS += --cache_dir $(CACHE_DIRECTORY)
  INCLUDE_PATHS+=$(CACHE_DIRECTORY)
endif

# Used only for OCaml extraction, not krml extraction
# OCaml or Plugin
FSTAR_ML_CODEGEN ?= OCaml

# Uncomment the definition of PROFILE below, if you want some basic
# profiling of F* runs It will report the time spent
# on typechecking your file And the time spent in SMT, which is
# included in the total typechecking time

# PROFILE=--profile YOUR_FILE --profile_component 'FStar.Universal.tc_source_file FStar.SMTEncoding'
FSTAR_OPTIONS += $(PROFILE)

# List the roots from where all dependencies are computed
FSTAR_FILES ?= $(wildcard $(addsuffix /*.fst,$(SRC_DIRS)) $(addsuffix /*.fsti,$(SRC_DIRS)))

FSTAR_OPTIONS += $(OTHERFLAGS) $(addprefix --include ,$(INCLUDE_PATHS)) --cache_checked_modules --warn_error @241

# Passing RESOURCEMONITOR=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(RESOURCEMONITOR),)
	ifeq ($(shell which runlim),)
		_ := $(error $(NO_RUNLIM_ERR)))
	endif
	ifneq ($(MONID),)
		MONPREFIX=$(MONID).
	endif
	RUNLIM=runlim -p -o $@.$(MONPREFIX)runlim
endif

FSTAR=$(RUNLIM) $(FSTAR_HOME)/bin/fstar.exe $(SIL) $(FSTAR_OPTIONS)

FSTAR_DEP_FILE ?= .depend

$(FSTAR_DEP_FILE): $(FSTAR_FILES)
	$(call msg, "DEPEND")
ifneq (,$(OUTPUT_DIRECTORY))
	mkdir -p $(OUTPUT_DIRECTORY)
endif
ifneq (,$(CACHE_DIRECTORY))
	mkdir -p $(CACHE_DIRECTORY)
endif
	$(Q)true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(FSTAR) $(FSTAR_DEP_OPTIONS) --dep full @$@.rsp --output_deps_to $@.aux
	mv $@.aux $@

include $(FSTAR_DEP_FILE)

$(ALL_CHECKED_FILES): %.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(Q)$(RUNLIM) $(FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

verify: $(ALL_CHECKED_FILES)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

# Extraction

$(ALL_ML_FILES): %.ml:
	$(FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(FSTAR_ML_CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))

$(ALL_KRML_FILES): %.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch -c $@

.PHONY: all verify %.fst-in %.fsti-in
