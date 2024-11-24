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

// Safety assert
ast_weak:             assert property (@(posedge clk) 1 |-> 1 ##[0:$] !$onehot0(state));

// Liveness asserts
ast_strong:           assert property (@(posedge clk) 1 |-> strong(1 ##[0:$] !$onehot0(state)));
ast_strong_equiv:     assert property (@(posedge clk) 1 |-> s_eventually(!$onehot0(state)));

endmodule
