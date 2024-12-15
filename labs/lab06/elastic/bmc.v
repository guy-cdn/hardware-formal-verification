module bmc(clk, rst, x, y);

input clk, rst;
input reg[63:0] x;
input reg[63:0] y;
reg[2:0] cnt;

// A bunch of numbers. All are primes, except for the last one.
localparam reg[127:0] numbers[0:7] = { 
    128'd10000000141,
    128'd10000000141,
    128'd10000000141,
    128'd10000000141,
    128'd10000000141,
    128'd10000000141,
    128'd10000000141,
    128'd10000000142 };

always @(posedge clk) begin
  if (~rst) begin
      cnt <= 3'd0;
  end else begin
      cnt <= cnt + 1'd1;
  end
end

factor: cover property (@(posedge clk) x>1 && y>1 && x*y == numbers[cnt]);

endmodule
