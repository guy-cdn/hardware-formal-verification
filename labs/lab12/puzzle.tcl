analyze -sv09 puzzle.v
elaborate -bbox_mul 128
reset ~rst
clock clk

prove -all -engine B
