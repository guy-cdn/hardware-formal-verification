module bmc(clk, rst, x, y);

input clk, rst;
input reg[63:0] x;
input reg[63:0] y;
reg[2:0] cnt;
reg[63:0] state;

// A bunch of numbers. All are primes, except for the last one.
localparam reg[127:0] numbers[0:7] = { 
    128'd8191,
    128'd131071,
    128'd524827,
    128'd400000043,
    128'd400000009,
    128'd400000067,
    128'd400000091,
    128'd2147483648 };

always @(posedge clk) begin
  if (~rst) begin
      cnt <= 3'd0;
      state <= 64'd1;
  end else begin
      cnt <= cnt + 1'd1;
      state <= state + x;
  end
end

factor: cover property (@(posedge clk) x>1 && y>1 && x*y == numbers[cnt]);
identity: assert property (@(posedge clk) (state-x)*(state+x) == state*state-x*x);

endmodule
