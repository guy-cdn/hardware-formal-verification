module test(clk, A, B, C);

input clk, A, B, C;

property P1;
  @(posedge clk) A ##1 B ##2 C;
endproperty

property P2;
  @(posedge clk) A;
endproperty

property P3;
  @(posedge clk) 1 ##1 B;
endproperty

property P4;
  @(posedge clk) 1 ##3 C;
endproperty

A1: assert property (P1);
A2: assume property (P2);
A3: assume property (P3);
A4: assume property (P4);

//B1: assume property (P1);
//B2: assert property (P2);
//B3: assert property (P3);
//B4: assert property (P4);

endmodule
