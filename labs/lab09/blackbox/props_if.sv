// Define instruction fetch properties here. 
module if_props(clk, rst, instr_req_o, instr_gnt_i);

  input clk;
  input rst;
  input instr_req_o;
  input instr_gnt_i;
  
  req_until_gnt: assert property (@(posedge clk) instr_req_o & ~instr_gnt_i |=> instr_req_o);

endmodule

// Bind the above module to the ibex_if_stage module.
bind ibex_if_stage if_props if_props_i(clk_i, rst_ni, instr_req_o, instr_gnt_i);
