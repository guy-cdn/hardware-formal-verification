module unique_prop(clk, rst, rvfi_valid, rvfi_order);

  input           clk;
  input           rst;
  input           rvfi_valid;
  input reg[63:0] rvfi_order;

  wire      en;           // When high for the first time, save rvfi_order
  reg       saved;        // Indicates whether order is saved in saved_order
  reg[63:0] saved_order;  // Saved rvfi_order
  reg       uniq;         // Indicates whether order is unique

  always @(posedge clk) begin
      if (!rst) begin 
          uniq <= 1'b1;
          saved <= 1'b0;
      end else if (rvfi_valid && !saved && en) begin
          saved_order <= rvfi_order;
          saved <= 1'b1;
      end else if (saved && rvfi_valid) begin
          uniq <= rvfi_order != saved_order;
      end
  end

  uniq_ast: assert property (@(posedge clk) uniq);

endmodule

// Bind the above module to the ibex_if_stage module.
bind ibex_top unique_prop prop_i(clk_i, rst_ni, rvfi_valid, rvfi_order);
