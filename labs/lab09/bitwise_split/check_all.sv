// Define a register check property for all registers
module register_prop(clk, rst, 
                     rvfi_valid,
                     rvfi_rd_addr, 
                     rvfi_rd_wdata, 
                     rvfi_rs1_addr, 
                     rvfi_rs1_rdata,
                     rvfi_rs2_addr, 
                     rvfi_rs2_rdata);

  input           clk;
  input           rst;
  input           rvfi_valid;
  input reg[4:0]  rvfi_rd_addr;
  input reg[31:0] rvfi_rd_wdata;
  input reg[4:0]  rvfi_rs1_addr;
  input reg[31:0] rvfi_rs1_rdata;
  input reg[4:0]  rvfi_rs2_addr;
  input reg[31:0] rvfi_rs2_rdata;

  reg[31:0] data; // Last data written to x_index
  reg written;    // Indicator whether data was written to x_index
  reg consistent; // Indicator for consistency of write/read to x_index
  reg[4:0] index; // Nondeterministic choice for the register index

  always @(posedge clk) begin
      if (!rst) begin 
          // Initial values
          written <= 1'b0;
          consistent <= 1'b1;
      end else if (rvfi_valid) begin
          if (rvfi_rd_addr == index) begin
              // Data is written to x_index, store written value in data
              data <= rvfi_rd_wdata;
              written <= 1'b1;
          end
          if (written && rvfi_rs1_addr == index) begin
              // Data is read from x_index, check consistency with stored data
              consistent <= data == rvfi_rs1_rdata;
          end else if (written && rvfi_rs2_addr == index) begin
              // Data is read from x_index, check consistency with stored data
              consistent <= data == rvfi_rs2_rdata;
          end
      end
  end

  consistent_x: assert property (@(posedge clk) consistent);
  stable_index: assume property (@(posedge clk) 1 ##1 $stable(index));
  positive_index: assume property (@(posedge clk) index != 5'd0);

endmodule

// Bind the above module to the ibex_if_stage module.
bind ibex_top register_prop prop_i(clk_i, rst_ni,
                                   rvfi_valid, 
                                   rvfi_rd_addr, 
                                   rvfi_rd_wdata, 
                                   rvfi_rs1_addr, 
                                   rvfi_rs1_rdata,
                                   rvfi_rs2_addr, 
                                   rvfi_rs2_rdata);
