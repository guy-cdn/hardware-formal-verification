// Define load store property.
module load_store_prop(clk, data_req_o, data_gnt_i, data_we_o);

  input clk;
  input data_req_o;
  input data_gnt_i;
  input data_we_o;
    
  // *************************
  // ********* NOTE **********
  // *************************
  // NOTE: You need to replace <SVA expression> below with an actual SVA
  // expression that captures the specification given in the home assignment.
  // You should use the signals defined in this module in the SVA expression.
  write_enable_ok: assert property (<SVA expression>);

endmodule

// Bind the above module to the ibex_load_store_unit module.
bind ibex_load_store_unit load_store_prop load_store_prop_i(clk_i, data_req_o, data_gnt_i, data_we_o);
