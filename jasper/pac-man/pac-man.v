// A module describing a PacMan game
module pacman #(parameter WIDTH = 8, HEIGHT = 8) (
    input  logic clk,                   // Clock signal
    input  logic rst,                   // Reset signal
    input  logic [1:0] move,            // Move signal: 00=up, 01=down, 10=left, 11=right
    output logic [WIDTH-1:0] pacman_x,  // Pac-Man X position
    output logic [HEIGHT-1:0] pacman_y, // Pac-Man Y position
    output logic [WIDTH-1:0] ghost_x,   // Ghost X position
    output logic [HEIGHT-1:0] ghost_y,  // Ghost Y position
    output logic [WIDTH-1:0][HEIGHT-1:0] walls,  // Wall positions (1 = wall, 0 = free)
    output logic [WIDTH-1:0][HEIGHT-1:0] candies, // Candy positions (1 = candy, 0 = empty)
    output logic catch                  // Indicator for the event that the ghost catches Pac-Man
);

    // Pac-Man position registers
    logic [WIDTH-1:0] pacman_x_reg, pacman_x_next;
    logic [HEIGHT-1:0] pacman_y_reg, pacman_y_next;

    // Ghost position registers
    logic [WIDTH-1:0] ghost_x_reg, ghost_x_next;
    logic [HEIGHT-1:0] ghost_y_reg, ghost_y_next;

    // Wall and candy initialization logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Initialize walls: Surround the grid with walls and add some internal walls.
            for (integer i = 0; i < WIDTH; i = i + 1) begin
                for (integer j = 0; j < HEIGHT; j = j + 1) begin
                    walls[i][j] <= 0;
                end
            end
            for (integer i = 0; i < WIDTH; i = i + 1) begin
                walls[i][0] <= 1;         // Top row
                walls[i][HEIGHT-1] <= 1;  // Bottom row
            end
            for (integer i = 0; i < HEIGHT; i = i + 1) begin
                walls[0][i] <= 1;         // Left column
                walls[WIDTH-1][i] <= 1;   // Right column
            end

            // Internal walls.  Assumes HEIGHT >= 6, WIDTH >= 7. A compilation
            // error will occur if these conditions aren't met.
            walls[2][2] <= 1;
            walls[3][3] <= 1;
            walls[4][4] <= 1;
            walls[5][5] <= 1;
            walls[5][6] <= 1;

            // Initialize candies (place candies at random locations)
            for (integer i = 0; i < WIDTH; i = i + 1) begin
                for (integer j = 0; j < HEIGHT; j = j + 1) begin
                    if (!walls[i][j])  // Only place candies in free cells
                        candies[i][j] <= 1;
                    else
                        candies[i][j] <= 0;  // No candies on walls
                end
            end

        end else if (candies[pacman_x_reg][pacman_y_reg]) begin
            // Pac-Man collects candy when moving over it
            candies[pacman_x_reg][pacman_y_reg] <= 0;
        end
    end

    // Pac-Man movement logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Start Pac-Man at (1,1)
            pacman_x_reg <= 1;
            pacman_y_reg <= 1;
        end else begin
            pacman_x_reg <= pacman_x_next;
            pacman_y_reg <= pacman_y_next;
        end
    end

    // Catch logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            catch <= 0;
        end else begin
            catch <= catch || (ghost_x_reg == pacman_x_reg && ghost_y_reg == pacman_y_reg);
        end
    end


    // Ghost movement logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Start Ghost at (WIDTH-2, HEIGHT-2)
            ghost_x_reg <= WIDTH-2;
            ghost_y_reg <= HEIGHT-2;
        end else begin
            ghost_x_reg <= ghost_x_next;
            ghost_y_reg <= ghost_y_next;
        end
    end

    // Determine next position for Pac-Man
    always_comb begin
        pacman_x_next = pacman_x_reg;
        pacman_y_next = pacman_y_reg;

        case (move)
            2'b00: if (pacman_y_reg > 0 && !walls[pacman_x_reg][pacman_y_reg-1])
                      pacman_y_next = pacman_y_reg - 1; // Move up
            2'b01: if (pacman_y_reg < HEIGHT-1 && !walls[pacman_x_reg][pacman_y_reg+1])
                      pacman_y_next = pacman_y_reg + 1; // Move down
            2'b10: if (pacman_x_reg > 0 && !walls[pacman_x_reg-1][pacman_y_reg])
                      pacman_x_next = pacman_x_reg - 1; // Move left
            2'b11: if (pacman_x_reg < WIDTH-1 && !walls[pacman_x_reg+1][pacman_y_reg])
                      pacman_x_next = pacman_x_reg + 1; // Move right
        endcase
    end

    // Simple Ghost movement logic
    always_comb begin
        ghost_x_next = ghost_x_reg;
        ghost_y_next = ghost_y_reg;

        // Basic random movement logic: check for walls before moving
        if (ghost_x_reg > 0 && !walls[ghost_x_reg-1][ghost_y_reg])
            ghost_x_next = ghost_x_reg - 1; // Move left
        else if (ghost_y_reg > 0 && !walls[ghost_x_reg][ghost_y_reg-1])
            ghost_y_next = ghost_y_reg - 1; // Move up
        else if (ghost_x_reg < WIDTH-1 && !walls[ghost_x_reg+1][ghost_y_reg])
            ghost_x_next = ghost_x_reg + 1; // Move right
        else if (ghost_y_reg < HEIGHT-1 && !walls[ghost_x_reg][ghost_y_reg+1])
            ghost_y_next = ghost_y_reg + 1; // Move down
    end

    // Output assignments
    assign pacman_x = pacman_x_reg;
    assign pacman_y = pacman_y_reg;
    assign ghost_x = ghost_x_reg;
    assign ghost_y = ghost_y_reg;

endmodule
