module toy(clk, rst, en, x, z, out);

input clk, rst, en;
input reg[2:0] x;
input reg[2:0] z;
output reg[5:0] out;
reg [5:0] tmp1;
reg [5:0] tmp2;

always @(posedge clk) begin
  if (~rst) begin
    out <= 6'd0;
    tmp1 <= 6'd0;
    tmp2 <= 6'd0;
  end else if (en) begin
    out <= tmp1 - tmp2;
    tmp1 <= x * x;
    tmp2 <= z * z;
  end
end

endmodule
