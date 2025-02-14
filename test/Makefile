SUBDIRS += bug-reports

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

$(OUTPUT_DIR)/Example_Unreachable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml)
