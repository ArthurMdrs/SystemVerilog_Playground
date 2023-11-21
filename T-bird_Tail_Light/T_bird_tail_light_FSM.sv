/*
    This is an implementation of the Finite-State Machine used to control
    the Ford Thunderbird tail lights. 

    There are 6 lights, each represented by a 1-bit output: LA, LB, LC, 
    RA, RB and RC.

    The inputs are:
    - Asynchronous active-low reset;
    - Positive edge sensitive clock;
    - LEFT, RIGHT and HAZ, the inputs from the car panel.

    The states are:
    - IDLE, the FSM waits for an input;
    - L1, L2 and L3, for when LEFT is pressed;
    - R1, R2 and R3, for when RIGHT is pressed;
    - LR3, the hazard light is on.

    The parameter state_time represents the time, in seconds, that the
    FSM stays in a state. The FSM stays in each state for state_time s 
    or until HAZ high is detected. The time scale must be informed as a 
    command line argument or added to the module code. 
*/

module T_bird_tail_light_FSM #(
    real state_time = 0.6667, // seconds
    real clock_period = 2000 // nanoseconds
) (
    input  logic rst_n, clk,
    input  logic LEFT, RIGHT, HAZ, 
    output logic LA, LB, LC, RA, RB, RC
);

    // Goal value for the counter
    localparam int state_count = int'(state_time*1s / (clock_period*1ns) - 1);

    // Import package with typedef and declare state
    import T_bird_tail_light_FSM_pkg::*;
    state_t state, n_state;

    // The counter
    logic [$clog2(state_count)-1:0] counter;
    // "Do not wait" flag will make FSM skip the counter
    logic do_not_wait;

    // Counter logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter <= 0;
        else if (do_not_wait == 1 || counter >= state_count)
            counter <= 0;
        else
            counter <= counter + 1;
    end

    // Do_not_wait logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            do_not_wait <= 1;
        else if (n_state != IDLE)
            do_not_wait <= 0;
    end

    // Update state logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else if (do_not_wait == 1) begin
            state <= n_state;
            // $display("%t Did not wait.", $realtime);
        end else if (counter >= state_count) begin
            state <= n_state;
        end
    end

    // Next-state logic
    always_comb begin
        n_state = state;
        unique case (state)
            IDLE: begin
                if ( HAZ ||  LEFT &&  RIGHT) begin
                    n_state = LR3;
                end else if (!HAZ &&  LEFT && !RIGHT) begin
                    n_state = L1;
                end else if (!HAZ && !LEFT &&  RIGHT) begin
                    n_state = R1;
                end
            end
            L1: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = L2;
                end
            end
            L2: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = L3;
                end
            end
            L3: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = IDLE;
                end
            end
            LR3: begin
                n_state = IDLE;
            end
            R1: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = R2;
                end
            end
            R2: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = R3;
                end
            end
            R3: begin
                if (HAZ) begin
                    n_state = LR3;
                end else if (!HAZ) begin
                    n_state = IDLE;
                end
            end
        endcase
    end

    // Output logic
    always_comb begin
        unique case (state)
            IDLE: begin
                {LC, LB, LA, RA, RB, RC} = 6'b000_000;
            end
            L1: begin
                {LC, LB, LA, RA, RB, RC} = 6'b001_000;
            end
            L2: begin
                {LC, LB, LA, RA, RB, RC} = 6'b011_000;
            end
            L3: begin
                {LC, LB, LA, RA, RB, RC} = 6'b111_000;
            end
            LR3: begin
                {LC, LB, LA, RA, RB, RC} = 6'b111_111;
            end
            R1: begin
                {LC, LB, LA, RA, RB, RC} = 6'b000_100;
            end
            R2: begin
                {LC, LB, LA, RA, RB, RC} = 6'b000_110;
            end
            R3: begin
                {LC, LB, LA, RA, RB, RC} = 6'b000_111;
            end
        endcase
    end

endmodule