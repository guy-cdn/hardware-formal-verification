# Analyze design and property files
analyze -sv09 -f ibex_core.f props_if.sv

# Elaborate design and properties
elaborate -top ibex_top \
    -bbox_m ibex_cs_registers \
    -bbox_m ibex_wb_stage \
    -bbox_m ibex_load_store_unit \
    -bbox_m ibex_id_stage \
    -bbox_m ibex_pmp \
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

# Set up proof
set_engine_mode M
set_prove_orchestration off
set_prove_verbosity 8

# Prove the property
prove -prop {<embedded>::ibex_top.u_ibex_core.if_stage_i.if_props_i.req_until_gnt}
