# Makefile for POSIX C99 UDP runtime harness for SWIM-Lean
# Targets macOS (clang) and Linux (gcc/clang)

CC ?= clang
CFLAGS ?= -std=c99 -Wall -Wextra -O2 -g

# 1. Locate Lean toolchain via elan
LEAN_BIN ?= $(shell elan which lean 2>/dev/null || which lean)
ifeq ($(strip $(LEAN_BIN)),)
    $(error "Unable to locate Lean binary via 'elan which lean' or 'which lean'.")
endif

# Lean sysroot, include, and library directories
LEAN_SYSROOT := $(shell $(LEAN_BIN) --print-prefix)
LEAN_INCLUDE := $(LEAN_SYSROOT)/include
LEAN_LIB     := $(LEAN_SYSROOT)/lib/lean

PROJECT_ROOT := $(abspath ..)
LAKE_BUILD   := $(PROJECT_ROOT)/.lake/build
SWIM_LIB     := $(LAKE_BUILD)/lib/libswim_SwimCore.a

TARGET       := swim_node
LOADGEN      := loadgen
SRCS         := main.c
OBJS         := $(SRCS:.c=.o)

INCLUDES     := -I$(LEAN_INCLUDE)
LDFLAGS      := -L$(LAKE_BUILD)/lib -lswim_SwimCore -L$(LEAN_LIB) -lleanshared -Wl,-rpath,$(LEAN_LIB)

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
    LDFLAGS += -lm -lpthread -ldl
endif

.PHONY: all clean build-lean test loadtest

all: $(TARGET) $(LOADGEN)

build-lean:
	@echo "Checking/building Lean SwimCore static library..."
	cd $(PROJECT_ROOT) && lake build SwimCore:static

$(SWIM_LIB): build-lean

%.o: %.c swim_exports.h
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

$(TARGET): main.o $(SWIM_LIB)
	$(CC) $(CFLAGS) main.o $(LDFLAGS) -o $@

$(LOADGEN): loadgen.o $(SWIM_LIB)
	$(CC) $(CFLAGS) loadgen.o $(LDFLAGS) -o $@

test: $(TARGET)
	@echo "Running local smoke test (2 nodes exchanging pings/acks)..."
	./$(TARGET) --id 1 --port 19001 --ticks 10 & PID1=$$!; \
	./$(TARGET) --id 2 --port 19002 --peer 1:127.0.0.1:19001 --ticks 10 & PID2=$$!; \
	wait $$PID1 && wait $$PID2
	@echo "Local smoke test passed successfully!"

loadtest: $(TARGET) $(LOADGEN)
	chmod +x run_experiment.sh && ./run_experiment.sh

clean:
	rm -f $(TARGET) $(LOADGEN) main.o loadgen.o
