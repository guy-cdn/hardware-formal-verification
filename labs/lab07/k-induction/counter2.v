module counter (
    input  clk,
    input  rst,
    output reg [3:0] c1,
    output reg [3:0] c2,
    output reg [31:0] c3,
    output reg [31:0] c4
);

always @(posedge clk or posedge rst) begin
    if (rst) begin
        c1 <= 0;
        c2 <= 0;
        c3 <= 0;
        c4 <= 0;
    end else begin
        c1 <= c1 + 1;
        c2 <= c2 + 1;
        c3 <= c3 + 1;
        c4 <= c4 + 1;
    end
end

ast: assert property (@(posedge clk) (&c1 |-> &c2) and (c3 == c4));

endmodule
