analyze -sv09 counter.v
elaborate 
clock clk
reset rst

prove -property counter.ast -engine Hps
