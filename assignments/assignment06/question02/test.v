module test(clk, rst, state);

input clk, rst;
output reg[2:0] state;

reg[31:0] counter;

always @(posedge clk) begin
  if (~rst) begin
    state <= 3'b010;
    counter <= 32'd0;
  end else begin
    counter <= counter + 1;
    if (counter[31]) begin
      state[0] <= ~state[0];
      state[1] <= state[0];
      state[2] <= state[1];
    end
  end
end

ast: assert property (@(posedge clk) state[0] == state[2]);

endmodule
