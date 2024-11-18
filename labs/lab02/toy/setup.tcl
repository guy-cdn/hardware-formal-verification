analyze -sv09 toy.v
elaborate
reset ~rst
clock clk

assert -name ast0 {@(posedge clk) state[0] |-> ~state[1]}
assert -name ast1 {@(posedge clk) en & state[2] |=> ~state[2]}
assert -name ast2 {@(posedge clk) ~en |=> $stable(state)}
assert -name ast3 {@(posedge clk) s_eventually(state == 3'b000)}
