module test(clk, A, C, D);

input clk, A, C, D;

property P1;
  @(posedge clk) A |=> strong(!D[*] ##1 C);
endproperty

property P2;
  @(posedge clk) A |=> !D s_until C;
endproperty

A1: assert property (P1);
A2: assume property (P2);

//B1: assume property (P1);
//B2: assert property (P2);

endmodule
