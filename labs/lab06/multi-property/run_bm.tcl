# Compile
analyze -sv09 bmc.v

# Elaborate, but don't blackbox multipliers where the sum of input bits is <= 128:
elaborate -bbox_mul 128

# Define reset and clock
reset ~rst
clock clk

# Prove all properties (there is only one property)
# Use engine Bm, which is a multi-property engine
# Use increased verbosity so as to see some extra information about the run
# Disable proof orchestration, to make sure only engine B runs
# Use unlimited time per property
prove -all -engine Bm -verbosity 11 -orch off -per_property_time_limit 0
