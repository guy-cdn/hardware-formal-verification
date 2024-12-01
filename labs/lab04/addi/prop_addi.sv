module addi_prop(clk, rst, rvfi_valid, rvfi_insn, rvfi_rd_addr, rvfi_rd_wdata, rvfi_rs1_rdata);

  input        clk;
  input        rst;
  input        rvfi_valid;
  input [31:0] rvfi_insn;
  input [4:0]  rvfi_rd_addr;
  input [31:0] rvfi_rd_wdata;
  input [31:0] rvfi_rs1_rdata;

  // Import definition of OPCODE_OP_IMM
  import ibex_pkg::*;
 
  ast_addi: assert property (@(posedge clk) 
              rvfi_valid &&
              rvfi_rd_addr != 5'b0 && // rd=x0 if NOP or HINT
              rvfi_insn[6:0] == OPCODE_OP_IMM &&
              rvfi_insn[14:12] == 3'b000 |-> 
                $signed(rvfi_rd_wdata) == $signed(rvfi_insn[31:20]) + $signed(rvfi_rs1_rdata));

endmodule

// Bind the above module to the ibex_core module.
bind ibex_core 
     addi_prop 
     addi_prop_i(clk_i, rst_ni, rvfi_valid, rvfi_insn, rvfi_rd_addr, rvfi_rd_wdata, rvfi_rs1_rdata);
