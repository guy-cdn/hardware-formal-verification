# Analyze design and property files
analyze -sv09 -f ibex_core.f load_store.sv

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

# Proof setup
source proof_setup.tcle

# The 'prop' variable is a Tcl variable that holds the name of the assert defined in load_store.sv
set prop <embedded>::ibex_top.u_ibex_core.load_store_unit_i.ls_props_i.write_enable_ok 
