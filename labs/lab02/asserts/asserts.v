module toy(clk, ok, en, gnt, req);

input clk, ok, en, gnt, req;

Q1: assert property (@(posedge clk) ok);
Q2: assert property (@(posedge clk) clk);
Q3: assert property (@(posedge clk) !(gnt && !req));
Q4: assert property (@(posedge clk) en |-> ok);
Q5: assert property (@(posedge clk) en |=> ok);
Q6: assert property (@(posedge clk) en |=> $past(ok));
Q7: assert property (@(posedge clk) en |=> $stable(ok));

endmodule
