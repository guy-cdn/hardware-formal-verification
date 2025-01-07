analyze -sv09 test.v
elaborate
reset ~rst
clock clk

set_prove_orchestration off

# Note: A previous version of this Tcl file contained the following command, which is now commented out.
# set_engine_mode B
