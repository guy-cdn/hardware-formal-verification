module puzzle(clk, rst, op, operand_a, operand_b, state, cycle);

input                   clk;
input                   rst;
input reg[1:0]          op;          // Operation in {*, + , -}
input reg[3:0]          operand_a;   // Nondeterministic 1st operand
input reg[3:0]          operand_b;   // Nondeterministic 2nd operand
output reg signed[63:0] state[8:0];  // Initially: [1, 2, ..., 9]
output reg[4:0]         cycle;       // Starts at 0 and increments by 1

always @(posedge clk) begin
  if (~rst) begin
    cycle <= 5'd0; // Reset cycle to 0
    // Reset state to [1, 2, 3, 4, 5, 6, 7, 8, 9]
    for (int i = 1; i <= 9; i++) begin state[i-1] <= i; end

  end else begin
    // Increment cycle
    cycle <= cycle + 5'd1;

    // Update state
    case (op)
        2'b00: state[operand_a] <= state[operand_a] * state[operand_b];
        2'b01: state[operand_a] <= state[operand_a] + state[operand_b];
        2'b10: state[operand_a] <= state[operand_a] - state[operand_b];
    endcase

    // Shift left numbers to the right of 'operand_a'
    for (int i = 0; i < 8; i++) begin
        if (i > operand_a) begin state[i] <= state[i+1]; end end
  end
end

// 'op' can only be either 2'b00, 2'b01, or 2'b10:
assume property (@(posedge clk) op != 2'b11);

// 'operand_a' and 'operand_b' are adjacent, and in the range for their cycle
assume property (@(posedge clk) operand_b == operand_a + 1);
assume property (@(posedge clk) operand_a >= 0);
assume property (@(posedge clk) cycle != 8 |-> operand_a < 8 - cycle);

// This has a cover trace iff the puzzle has a solution:
solution: cover property (@(posedge clk) cycle == 8 && state[0] == 2021);

endmodule
