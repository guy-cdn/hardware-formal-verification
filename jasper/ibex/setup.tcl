# Analyze design files
analyze -sv09 -f ibex_core.f \
    +define+IBEX_CFG_RV32M=ibex_pkg::RV32MSingleCycle \
    +define+IBEX_CFG_RV32B=ibex_pkg::RV32BOTEarlGrey \
    +define+IBEX_CFG_RegFile=ibex_pkg::RegFileFF

# Elaborate design and properties
elaborate -extract_covergroup -top ibex_top \
    -parameter ibex_core.RV32E 0 \
    -parameter ibex_core.BranchTargetALU 1 \
    -parameter ibex_core.WritebackStage 1 \
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

#Set up Clocks and Resets
clock clk_i
reset !rst_ni
