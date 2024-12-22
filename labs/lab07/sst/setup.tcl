analyze -sv09 counter.v
elaborate 
clock clk
reset rst

# Generate a counterexample to k-induction, k=5
prove -property counter.ast -sst 5

# Visualize the counterexample
visualize -violation -property <embedded>::counter.ast -new_window
