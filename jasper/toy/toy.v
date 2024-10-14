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


// Properties
property reachable_010_prop;
  @(posedge clk) (state == 3'b010);
endproperty
property reachable_111_prop;
  @(posedge clk) (state == 3'b111);
endproperty
property reachable_110_prop;
  @(posedge clk) (state == 3'b110);
endproperty
property onehot0_prop;
  @(posedge clk) ($onehot0(state));
endproperty
property eventually_wrap_prop;
  @(posedge clk) (s_eventually(state == 3'b000));
endproperty
property eventually_en_prop;
  @(posedge clk) (1 |-> s_eventually(en));
endproperty

// Cover properties
reachable_010:        cover property (reachable_010_prop);
reachable_111:        cover property (reachable_111_prop);

// Assert properties
onehot0:              assert property (onehot0_prop);
eventually_wrap:      assert property (eventually_wrap_prop);

// Assume properties
not_reachable_110:    assume property (not reachable_110_prop);
eventually_en:        assume property (eventually_en_prop);

endmodule

