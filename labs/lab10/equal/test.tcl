# Compile and elaborate the SPEC design
check_sec -compile_context spec
analyze -sv09 test1.v
elaborate -bbox_mul 32

# Compile and elaborate the IMP design
check_sec -compile_context imp
analyze -sv09 test2.v
elaborate -bbox_mul 32

# Define reset and clock
reset ~rst
clock clk

# Define assumes needed for the verification
assume {@(posedge clk) en}

# Construct miter and mappings
check_sec -setup
