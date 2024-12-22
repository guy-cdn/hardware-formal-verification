# Same as setup.tcl (can be found in the same directory),
# only now the property has a large number of flops in the COI,
# so as to not make it trivial for BMC.
analyze -sv09 counter2.v
elaborate 
clock clk
reset rst

prove -property counter.ast -engine Hps
