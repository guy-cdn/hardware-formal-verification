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

// Concurrent property
property onehot0_prop;
  @(posedge clk) ($onehot0(state));
endproperty

// Assert
onehot0: assert property (onehot0_prop);

// An alternative way to define the concurrent property and the assert together:
onehot0_alt: assert property (@(posedge clk) $onehot0(state));

endmodule
