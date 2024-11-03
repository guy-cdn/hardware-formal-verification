module props(clk, rst, eg_valid, eg_ready);

input clk, rst, eg_valid, eg_ready;

endmodule

bind top props props_i(clk, rstN, eg_valid, eg_ready);
