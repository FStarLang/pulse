
ifeq ($(FSTAR_EXE),)
ifneq ($(FSTAR_HOME),)
FSTAR_EXE := $(FSTAR_HOME)/bin/fstar.exe
endif
endif

FSTAR_EXE ?= $(shell which fstar.exe)
FSTAR_EXE := $(FSTAR_EXE)

$(call need_exe, FSTAR_EXE)

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(CURDIR))
else
  PULSE_HOME := $(CURDIR)
endif
export PULSE_HOME
