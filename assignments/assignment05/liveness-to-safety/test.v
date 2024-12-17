module top (clk, rst, q, x, y, counter);

input clk,rst;

output reg [3:0]counter;
output reg q;
output reg x;
output reg y;

always @ (posedge clk) begin
  if (~rst) begin
    counter <= 6'b0;
    q <= 1'b1;
    x <= 1'b0;
    y <= 1'b0;
  end else begin
    counter <= counter + 1'b1;
    q <= (q && x && counter == 1) || (~q && y);
    x <= q && y;
    y <= ~x;
  end
end

liveness: assert property (@(posedge clk) s_eventually(always(q)));

endmodule
