.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	aster_common \
	ostd \
	ostd_specs \
	vstd_extra

# Disabled:
# 	demo

.PHONY: all verify $(VERIFICATION_TARGETS) fmt clean

$(VERIFICATION_TARGETS):
	cargo dv verify --targets $@

all: verify

verify:
	cargo dv verify --targets $(VERIFICATION_TARGETS)

fmt:
	cargo dv fmt

clean:
	cargo clean
