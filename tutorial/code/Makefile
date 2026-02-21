PULSE_ROOT ?= ../..
include $(PULSE_ROOT)/mk/test.mk

all: test-rust update-generated-sources

.PHONY: test-rust
test-rust:
	cargo test

.PHONE: update-generated-sources
update-generated-sources: update-algo-c update-algo-ml

.PHONE: update-algo-c
update-algo-c: $(addprefix $(OUTPUT_DIR)/,PulseTutorial_Algorithms.krml PulseTutorial_Algorithms_Client.krml PulseTutorial_Algorithms_Client_Print.krml FStar_Pervasives_Native.krml)
	mkdir -p $(OUTPUT_DIR)/algo
	$(KRML_EXE) -tmpdir $(OUTPUT_DIR)/algo \
		-header=$(PULSE_ROOT)/mk/krmlheader \
		-rst-snippets \
		-bundle 'PulseTutorial.Algorithms.Client=*' \
		-drop PulseTutorial.Algorithms.Client.Print \
		-no-prefix 'PulseTutorial.Algorithms.Client.*' \
		-o PulseTutorial_Algorithms_Client \
		$+
	cp $(OUTPUT_DIR)/algo/PulseTutorial_Algorithms_Client.c .

.PHONE: update-algo-ml
update-algo-ml: $(addprefix $(OUTPUT_DIR)/,PulseTutorial_Algorithms.ml)
	cp $+ .