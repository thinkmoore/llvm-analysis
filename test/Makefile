##===- rocoto/test/Makefile --------------------------------*- Makefile -*-===##
#
# Define the default test rule, which allows people to just type 'make test' in
# this directory.
#
##===----------------------------------------------------------------------===##

# The default target in this directory is the test:: target
.PHONY: test
test:: lit

LEVEL = ..
include $(LEVEL)/Makefile.common

include $(PROJ_SRC_DIR)/Makefile.lit
