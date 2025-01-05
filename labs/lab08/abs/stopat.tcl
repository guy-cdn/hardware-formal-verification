# Analyze design and property files
analyze -sv09 -f ibex_core.f props_if.sv

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

# Get a list of all instances under the u_ibex_core instance
set ibex_instances     [get_design_info -instance u_ibex_core -list instance]

# Get a list of all instances that refer to the instruction fetch stage
set if_stage_instances [get_design_info -list instance -filter if_stage_i -regexp]

# Put a stopat on all instances in ibex_instances that are not in if_stage_instances
foreach instance $ibex_instances {
    if {[lsearch -exact $if_stage_instances $instance] < 0} {
        stopat $instance
    }
}

# Make sure to copy props_if.sv to props.sv so that the property below is defined
prove -prop {<embedded>::ibex_top.u_ibex_core.if_stage_i.if_props_i.req_until_gnt} -engine M -verbosity 8 -orch off
