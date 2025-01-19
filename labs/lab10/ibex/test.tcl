check_sec -compile_context spec

# Analyze design and property files
analyze -sv09 -f ibex_core.f +define+RISCV_FORMAL=1 +define+RVFI=1

# Elaborate design and properties
elaborate -top ibex_top \
    -parameter ibex_core.RV32E 0 \
    -parameter ibex_core.BranchTargetALU 1 \
    -parameter ibex_core.WritebackStage 0 \
    -parameter ibex_core.ICache 1 \
    -parameter ibex_core.ICacheECC 1  \
    -parameter ibex_core.BranchPredictor 0 \
    -parameter ibex_core.DbgTriggerEn 1 \
    -parameter ibex_core.SecureIbex 1 \
    -parameter ibex_core.PMPEnable 1 \
    -parameter ibex_core.PMPGranularity 0 \
    -parameter ibex_core.PMPNumRegions 16 \
    -parameter ibex_core.MHPMCounterNum 10 \
    -parameter ibex_core.MHPMCounterWidth 32

check_sec -compile_context imp

# Analyze design and property files
analyze -sv09 -f ibex_core.f

# Elaborate design and properties
elaborate -top ibex_top \
    -parameter ibex_core.RV32E 0 \
    -parameter ibex_core.BranchTargetALU 1 \
    -parameter ibex_core.WritebackStage 0 \
    -parameter ibex_core.ICache 1 \
    -parameter ibex_core.ICacheECC 1  \
    -parameter ibex_core.BranchPredictor 0 \
    -parameter ibex_core.DbgTriggerEn 1 \
    -parameter ibex_core.SecureIbex 1 \
    -parameter ibex_core.PMPEnable 1 \
    -parameter ibex_core.PMPGranularity 0 \
    -parameter ibex_core.PMPNumRegions 16 \
    -parameter ibex_core.MHPMCounterNum 10 \
    -parameter ibex_core.MHPMCounterWidth 32

# Set up Clocks and Resets
clock clk_i
reset !rst_ni

# Create miter model
check_sec -setup

# Check interface
check_sec -interface

# The interface will fail due to primary output mismatch
# Examine and verify that the mismatch is on the RVFI primary outputs
check_sec -interface -unmapped -signal_type primary_output -spec

# Waive the unmapped RVFI primary outputs
check_sec -waive -waive_signal \
  [check_sec -interface -unmapped -signal_type primary_output -spec]

# Prove
check_sec -prove

# Signoff
check_sec -signoff
