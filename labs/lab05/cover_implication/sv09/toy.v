module toy(clk, rst, en, state);

input clk, rst, en;
output reg[2:0] state;

always @(posedge clk) begin
  if (~rst) begin
    state <= 3'b000;
  end else if (en) begin
    state[0] <= state == 3'b000;
    state[1] <= state[0];
    state[2] <= state[1];
  end
end

P1: cover property (@(posedge clk) state == 3'b001 ##1 state == 3'b010);
P2: cover property (@(posedge clk) state == 3'b001 |=> state == 3'b010);

endmodule
