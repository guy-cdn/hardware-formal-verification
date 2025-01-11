# Analyze design and property files
analyze -sv09 -f ibex_core.f props_controller.sv 

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
set_engine_mode B
set_prove_orchestration off

# Prove 'safe'
prove -property <embedded>::ibex_top.u_ibex_core.id_stage_i.controller_i.controller_props_i.safe -bg

# Prove 'live'
prove -property <embedded>::ibex_top.u_ibex_core.id_stage_i.controller_i.controller_props_i.live -bg
