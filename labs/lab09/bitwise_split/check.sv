// Define a register check property for register x7
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

  reg[31:0] data; // Last data written to x7
  reg written;    // Indicator whether data was written to x7
  reg[31:0] inconsistent; // Indicator for inconsistency of write/read to x7

  always @(posedge clk) begin
      if (!rst) begin 
          // Initial values
          written <= 1'b0;
          inconsistent <= 32'd0;
      end else if (rvfi_valid) begin
          if (rvfi_rd_addr == 5'd7) begin
              // Data is written to x7, store written value in data
              data <= rvfi_rd_wdata;
              written <= 1'b1;
          end
          if (written && rvfi_rs1_addr == 5'd7) begin
              // Data is read from x7, check consistency with stored data
              inconsistent <= data ^ rvfi_rs1_rdata;
          end else if (written && rvfi_rs2_addr == 5'd7) begin
              // Data is read from x7, check consistency with stored data
              inconsistent <= data ^ rvfi_rs2_rdata;
          end
      end
  end

consistent_x7: assert property (@(posedge clk) inconsistent == 32'd0);

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
