analyze -sv09 counter.v
elaborate 
clock clk
reset rst

# Will not converge
prove -property counter.ast -engine {mp hp n m am tri g} -orch off -time 1m

# Define and prove a helper
assert -name helper {@(posedge clk) c1 == c2}
prove -property helper -engine Hps -orch off

# Use the helper to prove the original assert
# Will converge
prove -property counter.ast -with_proven -engine Hps -orch off
