analyze -sv09 counter.v
elaborate 
clock clk
reset rst

# Generate a counterexample to k-induction, k=8
prove -property counter.ast -sst 8

# Visualize the counterexample
visualize -violation -property <embedded>::counter.ast -new_window

# Add and prove helper assert
assert -name helper1 {@(posedge clk) c1[2] == c2[2]}
prove -property helper1
assert -set_helper helper1

# Generate another counterexample to k-induction, k=8
prove -property counter.ast -sst 8

# Visualize the counterexample
visualize -violation -property <embedded>::counter.ast -new_window

# Add and prove helper assert
assert -name helper2 {@(posedge clk) c1[31:3] == c2[31:3] && c1[1:0] == c2[1:0]}
prove -property helper2
assert -set_helper helper2

# Generate another counterexample to k-induction, k=8
prove -property counter.ast -sst 8
