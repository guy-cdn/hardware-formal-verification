module leap(clk, rst, en, x, y);

input clk, rst;
input reg[1:0] en;
input reg[31:0] x;
input reg[31:0] y;
reg[127:0] state;

always @(posedge clk) begin
  if (~rst) begin
      state <= 17;
  end else if (en == 2'b00) begin
      state <= state + state;
  end else if (en == 2'b01) begin
      state <= state + state / 2;
  end else if (en == 2'b10) begin
      state <= state - 3;
  end else if (en == 2'b11) begin
      state <= state + 3;
  end
end

C1:  cover property (@(posedge clk) 128'h00000000000000000000000000000020==state);
C2:  cover property (@(posedge clk) 128'h00000000000000000000000000003e80==state);
C3:  cover property (@(posedge clk) 128'h0000000000000000000000000007cd6c==state);
C4:  cover property (@(posedge clk) 128'h00000000000000000000000003e6b4da==state);
C5:  cover property (@(posedge clk) 128'h0000000000000000000003e6b4d8fd34==state);
C6:  cover property (@(posedge clk) 128'h0000000000000000000f9ad363f4c331==state);
C7:  cover property (@(posedge clk) 128'h0000000000000000f9ad363f4c32d06a==state);
C8:  cover property (@(posedge clk) 128'h00000000000000000000000001f35a6d==state);
C9:  cover property (@(posedge clk) 128'h00000000000000000007cd69b1fa619d==state);
C10: cover property (@(posedge clk) 128'h0000000000000000000000001f35a6ca==state);
C11: cover property (@(posedge clk) 128'h0000000000000000000000003e6b4d91==state);
C12: cover property (@(posedge clk) 128'h00000000000000000000000000f9ad38==state);

endmodule
