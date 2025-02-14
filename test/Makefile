# SUBDIRS += bug-reports

PULSE_ROOT ?= ..
include $(PULSE_ROOT)/mk/test.mk

# FIXME: these extra karamel dependencies should be somehow
# automatically computed. I am just retaining them from the previous
# Makefile.

$(OUTPUT_DIR)/Example_Hashtable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml \
	Pulse_Lib_Vec.krml \
	Pulse_Lib_HashTable_Type.krml \
	Pulse_Lib_HashTable_Spec.krml \
	Pulse_Lib_HashTable.krml)

$(OUTPUT_DIR)/Example_MutableSlice.c: $(addprefix $(OUTPUT_DIR)/,\
	Pulse_Lib_MutableSlice.krml)

$(OUTPUT_DIR)/Example_Slice.c: $(addprefix $(OUTPUT_DIR)/,\
	Pulse_Lib_Slice.krml)

$(OUTPUT_DIR)/example/mutableslice.rs: $(addprefix $(OUTPUT_DIR)/,\
	Example_MutableSlice.krml \
	Pulse_Lib_MutableSlice.krml)

$(OUTPUT_DIR)/example/slice.rs: $(addprefix $(OUTPUT_DIR)/,\
	Example_Slice.krml \
	Pulse_Lib_Slice.krml)

$(OUTPUT_DIR)/Example_Unreachable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml)

$(OUTPUT_DIR)/%.rs:
	$(call msg, "KRML RS", $(basename $(notdir $@)))
	$(KRML_EXE) -header=$(PULSE_ROOT)/mk/krmlheader -bundle $(basename $(notdir $<))=* -skip-compilation $+ -fkeep-tuples -tmpdir $(OUTPUT_DIR) -backend rust
