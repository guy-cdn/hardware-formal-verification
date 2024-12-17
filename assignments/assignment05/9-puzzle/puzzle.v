module puzzle (clk, rst, cells, direction);

input           clk, rst;
input reg[1:0]  direction;
output reg[3:0] cells[2:0][2:0];
reg[1:0]        empty_x; // x-position of the empty cell
reg[1:0]        empty_y; // y-position of the empty cell

always @ (posedge clk) begin
  if (~rst) begin
    cells[0][0] <= 8;
    cells[0][1] <= 7;
    cells[0][2] <= 0;
    cells[1][0] <= 6;
    cells[1][1] <= 5;
    cells[1][2] <= 4;
    cells[2][0] <= 3;
    cells[2][1] <= 2;
    cells[2][2] <= 1;
    empty_x <= 0;
    empty_y <= 2;
  end else begin
    if (direction == 2'b00 && empty_y > 3'd0) begin // left
        cells[empty_x][empty_y] <= cells[empty_x][empty_y-1];
        cells[empty_x][empty_y-1] <= 0;
        empty_y <= empty_y-1;
    end
    if (direction == 2'b01 && empty_y < 3'd2) begin // right
        cells[empty_x][empty_y] <= cells[empty_x][empty_y+1];
        cells[empty_x][empty_y+1] <= 0;
        empty_y <= empty_y+1;
    end
    if (direction == 2'b10 && empty_x > 3'd0) begin // up
        cells[empty_x][empty_y] <= cells[empty_x-1][empty_y];
        cells[empty_x-1][empty_y] <= 0;
        empty_x <= empty_x-1;
    end
    if (direction == 2'b11 && empty_x < 3'd2) begin // down
        cells[empty_x][empty_y] <= cells[empty_x+1][empty_y];
        cells[empty_x+1][empty_y] <= 0;
        empty_x <= empty_x+1;
    end
  end
end

wire solution = cells[0][0] == 1 &
                cells[0][1] == 2 &
                cells[0][2] == 3 &
                cells[1][0] == 4 &
                cells[1][1] == 5 &
                cells[1][2] == 6 &
                cells[2][0] == 7 &
                cells[2][1] == 8 &
                cells[2][2] == 0;

c: cover property (@(posedge clk) solution);

endmodule
