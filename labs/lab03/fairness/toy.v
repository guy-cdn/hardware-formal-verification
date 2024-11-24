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

// Assert
ast_liveness: assert property (@(posedge clk) s_eventually(state == 3'b000));

// Assume
fairness:     assert property (@(posedge clk) s_eventually(en));

endmodule
