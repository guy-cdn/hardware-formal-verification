module test(clk, rst, state);

input clk, rst;
output reg[2:0] state;

always @(posedge clk) begin
  if (~rst) begin
    state <= 3'b000;
  end else begin
    state[0] <= state == 3'b000;
    state[1] <= state[0];
    state[2] <= state[1];
  end
end

ast1: assert property (@(posedge clk) $onehot0(state));
ast2: assert property (@(posedge clk) state != 3'b110);

endmodule
