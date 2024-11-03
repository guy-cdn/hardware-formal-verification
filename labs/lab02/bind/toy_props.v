module toy_props(clk_, state_);

input clk_;
input reg[2:0] state_;

onehot0: assert property (@(posedge clk_) $onehot0(state_));

endmodule

// The 'clk' and 'state' are taken from the 'toy' module scope
bind toy toy_props toy_props_i(clk, state);
