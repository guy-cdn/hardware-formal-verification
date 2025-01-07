analyze -sv09 test.v
elaborate
reset ~rst
clock clk

set_prove_orchestration off
set_engine_mode B
