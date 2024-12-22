analyze -sv09 counter.v
elaborate  -bbox_mul 128
clock clk
reset rst

# Won't converge
prove -property counter.ast -engine Hps -orch off -time 30s

# Will converge
set_first_proof_attempt 17
prove -property counter.ast -engine Hps -orch off
