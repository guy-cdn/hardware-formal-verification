module counter (
    input  clk,
    input  rst,
    input[63:0] x,
    input[63:0] y,
    output reg [3:0] c1,
    output reg [3:0] c2
);

// N is a product of two large primes
localparam reg[127:0] N = 128'd100000002820000019881;

always @(posedge clk or posedge rst) begin
    if (rst) begin
        c1 <= 0;
        c2 <= 0;
    end else begin
        c1 <= c1 + 1;
        c2 <= c2 + 1;
    end
end

ast: assert property (@(posedge clk) (&c1 |-> &c2));
asm: assume property (@(posedge clk) (x>1 && y>1 && x*y == N));

endmodule
