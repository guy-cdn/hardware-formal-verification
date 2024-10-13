###########################################
# Setup
###########################################
analyze -sv09 -f ibex_core.f \
        -incdir ../vendor/lowrisc_ip/ip/prim/rtl/ \
        -incdir ../vendor/lowrisc_ip/dv/sv/dv_utils/ \
        +define+FORMAL +define+RISCV_FORMAL +define+RVFI
elaborate -top ibex_core
clock clk_i
reset ~rst_ni
