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

// Cover properties
reachable_010:        cover property (@(posedge clk) state == 3'b010);
reachable_111:        cover property (@(posedge clk) state == 3'b111);

// Assert properties
onehot0:              assert property (@(posedge clk) $onehot0(state));
eventually_wrap:      assert property (@(posedge clk) state[0] == 0);

endmodule
