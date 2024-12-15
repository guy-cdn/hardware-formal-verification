# Compile
analyze -sv09 bmc.v

# Elaborate, but don't blackbox multipliers where the sum of input bits is <= 128:
elaborate -bbox_mul 128

# Define reset and clock
reset ~rst
clock clk

# Prove all properties (there is only one property)
# Use engine B, which is a single property engine
# Use increased verbosity so as to see some extra information about the run
# Disable proof orchestration, to make sure only engine B runs
# The property has a cover trace of length 8, but reaching Trace Attempt 8 is hard
prove -all -engine B -verbosity 11 -orch off

# Clear result, so the next proof starts fresh
clear -result

# We can help the engine reach Trace Attempt 8 faster, but skipping the first 7 Trace Attempts
# This proof will now find the cover trace for the property much faster
set_first_trace_attempt 8
prove -all -engine B -verbosity 11 -orch off

