// Define two properties in the ibex_controller module.
//
// - A liveness property 'live' checking that if the controller is in state
//   DECODE then eventually it will exit that state.
// - A safety property 'safe' checking that if the controller is in state
//   DECODE then it will exit that state in the next 1000 cycles.
//
// Note: DECODE is the normal operation mode for the instruction decode state.

module controller_props(clk, rst, ctrl_fsm_cs);
   
  // Import definition of ctrl_fsm_e (state enums)
  import ibex_pkg::*;

  input clk;
  input rst;
  input ctrl_fsm_e ctrl_fsm_cs;
  
  // Properties
  live: assert property (@(posedge clk) ctrl_fsm_cs == DECODE |-> s_eventually(ctrl_fsm_cs != DECODE));
  safe: assert property (@(posedge clk) ctrl_fsm_cs == DECODE |-> 1 ##[0:1000] ctrl_fsm_cs != DECODE);

endmodule

// Bind the above module to the ibex_controller module.
bind ibex_controller controller_props controller_props_i(clk_i, rst_ni, ctrl_fsm_cs);
