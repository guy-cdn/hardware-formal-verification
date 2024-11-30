// An example file for how to define and bind properties to design modules.
// You will need to extend the interface with more inputs, if needed.
module my_props(clk, rst);

  input clk;
  input rst;
  
  // An example property.
  dummy: assert property (@(posedge clk) 1);

endmodule

// An example of binding the above module to the ibex_core module.
bind ibex_core my_props my_props_i(clk_i, rst_ni);
