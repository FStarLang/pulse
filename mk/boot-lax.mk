include mk/common.mk

.DEFAULT_GOAL := ocaml
$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)
$(call need, ROOTS, a list of roots for the dependency analysis)

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: all
all: verify ocaml

.PHONY: ocaml
ocaml: all-ml

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect
FSTAR_OPTIONS += $(OTHERFLAGS)
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --include "$(SRC)"
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --warn_error -321
ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR = $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%.checked.lax: LBL=$(basename $(basename $(notdir $@)))
%.checked.lax:
	$(call msg, "CHECK", $(LBL))
	$(FSTAR) --already_cached '*' $<
	touch -c $@  ## SHOULD NOT BE NEEDED

%.ml: FF=$(notdir $(subst .checked.lax,,$<))
%.ml: MM=$(basename $(FF))
%.ml: LBL=$(notdir $@)
# ^ HACK we use notdir to get the module name since we need to pass in
# the fst (not the checked file), but we don't know where it is, so this
# is relying on F* looking in its include path.
%.ml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $(FF) --already_cached '*' --codegen $(CODEGEN) --extract_module $(MM)
	touch -c $@  ## SHOULD NOT BE NEEDED

$(CACHE_DIR)/.depend$(TAG):
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(DEPFLAGS) --output_deps_to $@
	mkdir -p $(CACHE_DIR)

depend: $(CACHE_DIR)/.depend$(TAG)
include $(CACHE_DIR)/.depend$(TAG)

all-ml: $(ALL_ML_FILES)
all-checked: $(ALL_CHECKED_FILES)
