# Compile
analyze -sv09 leap.v

# Elaborate, but don't blackbox multipliers where the sum of input bits is <= 128:
elaborate -bbox_mul 128

# Define reset and clock
reset ~rst
clock clk

# Prove all properties (there is only one property)
# Use engine B and Bm
# Use increased verbosity so as to see some extra information about the run
# Disable proof orchestration, to make sure only engine B runs
prove -all -engine {B Bm} -verbosity 11 -orch off

# Clear result for the next proof
clear -result

# Prove all properties with engine L
prove -all -engine L -verbosity 11 -orch off
