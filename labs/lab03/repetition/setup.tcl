analyze -sv09 toy.v
elaborate
reset ~rst
clock clk

cover -name cover_length_17 {@(posedge clk) 1[*17]}
prove -property cover_length_17
visualize -property cover_length_17
