analyze -sv09 counter.v
elaborate 
clock clk
reset rst

# Generate a counterexample to k-induction, k=5
prove -property counter.ast -sst 5

# Visualize the counterexample
visualize -violation -property <embedded>::counter.ast -new_window

# Add and prove helper assert
assert -name c1_eq_c2 {@(posedge clk) c1 == c2}
prove -property c1_eq_c2

# Prove the original assert with the help of the helper assert
prove -property counter.ast -with_proven
