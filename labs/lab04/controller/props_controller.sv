// Define instruction fetch properties here. 
module controller_props(clk, rst, ctrl_fsm_cs);
   
  // Import definition of ctrl_fsm_e (state enums)
  import ibex_pkg::*;

  input clk;
  input rst;
  input ctrl_fsm_e ctrl_fsm_cs;
  
  // Check reachability of transitions from DECODE
  cov_dec_dec:       cover property (@(posedge clk) ctrl_fsm_cs == DECODE ##1 ctrl_fsm_cs == DECODE);
  cov_dec_flush:     cover property (@(posedge clk) ctrl_fsm_cs == DECODE ##1 ctrl_fsm_cs == FLUSH);
  cov_dec_dbg_taken: cover property (@(posedge clk) ctrl_fsm_cs == DECODE ##1 ctrl_fsm_cs == DBG_TAKEN_IF);
  cov_dec_irq_taken: cover property (@(posedge clk) ctrl_fsm_cs == DECODE ##1 ctrl_fsm_cs == IRQ_TAKEN);

endmodule

// Bind the above module to the ibex_if_stage module.
bind ibex_controller controller_props controller_props_i(clk_i, rst_ni, ctrl_fsm_cs);
