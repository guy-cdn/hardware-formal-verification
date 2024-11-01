// A module describing a PacMan game
module pacman #(parameter WIDTH = 6, HEIGHT = 6) (
    input  logic clk,                   // Clock signal
    input  logic rst,                   // Reset signal
    input  logic [1:0] pacman_move,     // Move signal: 00=up, 01=down, 10=left, 11=right
    output logic [WIDTH-1:0] pacman_x,  // Pac-Man X position
    output logic [HEIGHT-1:0] pacman_y, // Pac-Man Y position
    output logic [WIDTH-1:0] ghost_x,   // Ghost X position
    output logic [HEIGHT-1:0] ghost_y,  // Ghost Y position
    output logic [WIDTH-1:0][HEIGHT-1:0] candies, // Candy positions (1 = candy, 0 = empty)
    output logic caught                 // Indicator for the event that the ghost catches Pac-Man
);

    ////////////////////////////////
    // Pac-Man position registers //
    ////////////////////////////////
    logic [WIDTH-1:0] pacman_x_reg, pacman_x_next;
    logic [HEIGHT-1:0] pacman_y_reg, pacman_y_next;

    //////////////////////////////
    // Ghost position registers //
    //////////////////////////////
    logic [WIDTH-1:0] ghost_x_reg, ghost_x_next;
    logic [HEIGHT-1:0] ghost_y_reg, ghost_y_next;

    /////////////////////////////////////////
    // Wall and candy initialization logic //
    /////////////////////////////////////////
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Initialize candies (place candies at "random" locations)
            for (integer i = 0; i < WIDTH; i = i + 1) begin
                for (integer j = 0; j < HEIGHT; j = j + 1) begin
                    if (i % 3 == 0 || j % 3 == 1)
                        candies[i][j] <= 1;
                    else
                        candies[i][j] <= 0;
                end
            end

        end else if (candies[pacman_x_reg][pacman_y_reg]) begin
            // Pac-Man collects candy when moving over it
            candies[pacman_x_reg][pacman_y_reg] <= 0;
        end
    end

    ////////////////////////////
    // Pac-Man movement logic //
    ////////////////////////////
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

    //////////////////////////
    // Ghost movement logic //
    //////////////////////////
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Start Ghost at (WIDTH/2, HEIGHT/2)
            ghost_x_reg <= WIDTH/2;
            ghost_y_reg <= HEIGHT/2;
        end else begin
            ghost_x_reg <= ghost_x_next;
            ghost_y_reg <= ghost_y_next;
        end
    end

    /////////////////////////////////////////
    // Determine next position for Pac-Man //
    /////////////////////////////////////////
    always_comb begin
        pacman_x_next = pacman_x_reg;
        pacman_y_next = pacman_y_reg;

        case (pacman_move)
            2'b00: if (pacman_y_reg > 0)
                      pacman_y_next = pacman_y_reg - 1; // Move up
            2'b01: if (pacman_y_reg < HEIGHT-1)
                      pacman_y_next = pacman_y_reg + 1; // Move down
            2'b10: if (pacman_x_reg > 0)
                      pacman_x_next = pacman_x_reg - 1; // Move left
            2'b11: if (pacman_x_reg < WIDTH-1)
                      pacman_x_next = pacman_x_reg + 1; // Move right
        endcase
    end

    ///////////////////////////////////////
    // Determine next position for ghost //
    ///////////////////////////////////////
    always_comb begin
        ghost_x_next = ghost_x_reg;
        ghost_y_next = ghost_y_reg;

        // Basic movement logic
        if (ghost_x_reg > pacman_x_reg)
            ghost_x_next = ghost_x_reg - 1; // Move left
        else if (ghost_y_reg > pacman_y_reg)
            ghost_y_next = ghost_y_reg - 1; // Move up
        else if (ghost_x_reg < pacman_x_reg)
            ghost_x_next = ghost_x_reg + 1; // Move right
        else if (ghost_y_reg < pacman_y_reg)
            ghost_y_next = ghost_y_reg + 1; // Move down
    end

    /////////////////
    // Catch logic //
    /////////////////
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            caught <= 0;
        end else begin
            caught <= caught || (ghost_x_reg == pacman_x_reg && ghost_y_reg == pacman_y_reg);
        end
    end

    ////////////////////////
    // Output assignments //
    ////////////////////////
    assign pacman_x = pacman_x_reg;
    assign pacman_y = pacman_y_reg;
    assign ghost_x = ghost_x_reg;
    assign ghost_y = ghost_y_reg;

    ///////////////////////////
    // Concurrent Properties //
    ///////////////////////////
    property candies_update_prop;
    @(posedge clk) (1 ##1 $countones(candies) <= $past($countones(candies)));
    endproperty
    property collected_all_candies_prop;
    @(posedge clk) ($countones(candies) == 0);
    endproperty
    property win_prop;
    @(posedge clk) ($countones(candies) == 0 && !caught);
    endproperty

    /////////////////////////
    // Property Directives //
    /////////////////////////
    candies_update:        assert property (candies_update_prop);
    collected_all_candies: cover property  (collected_all_candies_prop);
    win:                   cover property  (win_prop);

endmodule
