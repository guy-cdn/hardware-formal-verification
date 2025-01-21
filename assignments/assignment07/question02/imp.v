module test(clk, rst, out);

input clk, rst;
output reg[9:0] out;
reg[9:0] tmp;
reg[31:0] cnt;

always @(posedge clk) begin
  if (~rst) begin
    out <= 10'd0;
    tmp <= 10'd0;
    cnt <= 32'd1;
  end else begin
    tmp <= tmp + cnt;
    out <= tmp;
    cnt <= cnt + 3;
  end
end

endmodule
