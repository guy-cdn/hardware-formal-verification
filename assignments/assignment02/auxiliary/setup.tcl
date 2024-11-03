# NOTE! You need to edit the path below to point to the Jasper installation.
set jasper "/path/to/jasper/installation"
set jasper "/home/guy/DS1/hg/trunk_clean6"

set source "${jasper}/doc/example_jasper_apps/designs/reference_design/verilog_sva/source/design"

analyze -sv09 $source/arbiter.v \
              $source/port_select.v \
              $source/bridge.v \
              $source/egress.v \
              $source/ingress.v \
              $source/top.v
analyze -sv09 props.v
elaborate
clock clk 
reset ~rstN 
