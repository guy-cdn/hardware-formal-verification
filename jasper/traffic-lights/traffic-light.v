// Note: the design contains a bug with respect to a specification that will be given in an assignment.

module traffic_light (
    input wire clk,             // Clock signal
    input wire rst,             // Reset signal
    input wire pedestrian_btn,  // Pedestrian request button
    output reg [1:0] car_light, // Car traffic light (3-bit: Red, Yellow, Green)
    output reg pedestrian_light // Pedestrian traffic light (1-bit: Red/Green)
);

// Define the states for car and pedestrian traffic light
typedef enum reg [1:0] {
    GREEN  = 2'b00,
    YELLOW = 2'b01,
    RED    = 2'b10
} state_t; 

state_t car_state, next_car_state;
state_t pedestrian_state, next_pedestrian_state;

// Timing parameters
parameter WAIT_TIME = 2;     // Car green light minimum time
parameter GREEN_TIME = 3;    // Car green light maximum time
parameter YELLOW_TIME = 1;   // Car yellow light time
parameter RED_TIME = 2;      // Time before pedestrian light turns green

reg [24:0] car_timer;        // Timer for state transitions
reg pedestrian_request;     // Register to store pedestrian button press

// Sequential logic, updating next states
always @(posedge clk or posedge rst) begin
    if (rst) begin
        car_state <= RED;
        pedestrian_state <= RED;
        car_timer <= 0;
        pedestrian_request <= 0;
    end else begin
        car_state <= next_car_state;
        pedestrian_state <= next_pedestrian_state;

        if (car_state != next_car_state) car_timer <= 0;
        else car_timer <= car_timer + 1;

        // Register the pedestrian button press
        if (pedestrian_btn)
            pedestrian_request <= 1;
    end
end

// Car traffic light state machine
always @(*) begin
    case (car_state)
        GREEN: begin
            if (pedestrian_request && car_timer >= WAIT_TIME)
                next_car_state = YELLOW;
            else if (car_timer >= GREEN_TIME)
                next_car_state = YELLOW;
            else
                next_car_state = GREEN;
        end
        YELLOW: begin
            if (car_timer >= YELLOW_TIME)
                next_car_state = RED;
            else
                next_car_state = YELLOW;
        end
        RED: begin
            if (car_timer >= RED_TIME)
                next_car_state = GREEN;
            else
                next_car_state = RED;
        end
        default: next_car_state = GREEN;
    endcase
end

// Pedestrian traffic light state machine
always @(*) begin
    case (pedestrian_state)
        GREEN: begin
            if (car_state == RED && car_timer >= RED_TIME-1)
                next_pedestrian_state = RED;
            else
                next_pedestrian_state = GREEN;
        end
        RED: begin
            if (next_car_state != RED || car_timer != 0)
                next_pedestrian_state = RED;
            else
                next_pedestrian_state = GREEN;
        end
        default: next_pedestrian_state = RED;
    endcase
end

// Traffic light outputs
always @(*) begin
    case (car_state)
        GREEN:   car_light = GREEN;          // Green light
        YELLOW:  car_light = YELLOW;         // Yellow light
        RED:     car_light = RED;            // Red light
        default: car_light = RED;            // Default to red
    endcase

    case (pedestrian_state)
        GREEN:   pedestrian_light = GREEN;   // Green light
        RED:     pedestrian_light = RED;     // Red light
        default: pedestrian_light = RED;     // Default to red
    endcase
end




assert property (@(posedge clk) disable iff (rst) (car_state == GREEN && car_timer == 0 |-> $past(car_state) ==  RED));
assert property (@(posedge clk) disable iff (rst) !(car_state == GREEN && pedestrian_state == GREEN));

// Red car light can only change to green.
// Yellow car light can only change to red.
// Green car light can only change to yellow.
assert property (@(posedge clk) disable iff (rst) (car_light == RED |=> car_light == RED || car_light == GREEN));
assert property (@(posedge clk) disable iff (rst) (car_light == GREEN |=> car_light == YELLOW || car_light == GREEN));
assert property (@(posedge clk) disable iff (rst) (car_light == YELLOW |=> car_light == YELLOW || car_light == RED));

// Car light is never stuck at any color.
// Pedestrian light is never stuck at any color.
assert property (@(posedge clk) disable iff (rst) (s_eventually(pedestrian_light == GREEN)));
assert property (@(posedge clk) disable iff (rst) (s_eventually(pedestrian_light == RED)));
assert property (@(posedge clk) disable iff (rst) (s_eventually(car_light == GREEN)));
assert property (@(posedge clk) disable iff (rst) (s_eventually(car_light == RED)));
assert property (@(posedge clk) disable iff (rst) (s_eventually(car_light == YELLOW)));

// Always at least one light (car or pedestrian) is red.
assert property (@(posedge clk) disable iff (rst) (car_light == RED || pedestrian_light == RED));

// If one light is green, then the other is red
assert property (@(posedge clk) disable iff (rst) (pedestrian_state == GREEN |-> car_state == RED));
assert property (@(posedge clk) disable iff (rst) (car_light == GREEN |-> pedestrian_light == RED));

// If pedestrian light is green, then car light is red.
assert property (@(posedge clk) disable iff (rst) (pedestrian_light == GREEN |-> car_light == RED));

// If pedestrian light is green, then car light in the previous cycle is red.
assert property (@(posedge clk) disable iff (rst) (pedestrian_light == GREEN |-> $past(car_light) == RED));
// If car light is green, then pedestrian light in the previous cycle is red.
assert property (@(posedge clk) disable iff (rst) (car_light == GREEN |-> $past(pedestrian_light) == RED));

// Legal states
assert property (@(posedge clk) disable iff (rst) (car_light == RED | car_light == GREEN || car_light == YELLOW));
assert property (@(posedge clk) disable iff (rst) (pedestrian_light == RED | pedestrian_light == GREEN));

// Time is reset when transitioning to new color
assert property (@(posedge clk) disable iff (rst) (car_state == GREEN |=> car_state == GREEN || car_timer == 0));
assert property (@(posedge clk) disable iff (rst) (car_state == YELLOW |=> car_state == YELLOW || car_timer == 0));
assert property (@(posedge clk) disable iff (rst) (car_state == RED |=> car_state == RED || car_timer == 0));

// Pedestrian can't harass car
assert property (@(posedge clk) disable iff (rst)
   (pedestrian_request && car_state==GREEN && car_timer < WAIT_TIME |=> car_state == GREEN));

endmodule

