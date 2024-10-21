analyze -sv09 toy.v
elaborate
reset ~rst
clock clk

assert -name onehot0 {$onehot0(state)}


