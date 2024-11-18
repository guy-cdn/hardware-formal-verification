module toy(clk, ok, en, gnt, req, A, B);

input clk, ok, en, gnt, req, A, B;

P1: assert property (@(posedge clk) ok);
P2: assert property (@(posedge clk) en |-> ok);
P3: assert property (@(posedge clk) en |=> ok);
P4: assert property (@(posedge clk) en |=> $past(ok));
P5: assert property (@(posedge clk) en |=> $stable(ok));
P6: assert property (@(posedge clk) en |=> s_eventually(ok));
P7: assert property (@(posedge clk) A ##2 B);
P8: assert property (@(posedge clk) A ##[1:3] B);
P9: assert property (@(posedge clk) A[*4]);

endmodule
