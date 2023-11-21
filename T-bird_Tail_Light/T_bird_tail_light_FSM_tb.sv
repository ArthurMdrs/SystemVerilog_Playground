module T_bird_tail_light_FSM_tb;

    // DUT signals
    logic rst_n, clk;
    logic LEFT, RIGHT, HAZ; 
    logic LA, LB, LC, RA, RB, RC;

    // DUT parameters
    localparam real state_time = 0.6667;

    // import T_bird_tail_light_FSM_pkg::*;

    // The DUT
    T_bird_tail_light_FSM #(.state_time(state_time)) DUT (.rst_n, .clk, .LEFT, .RIGHT, .HAZ, .LA, .LB, .LC, .RA, .RB, .RC);

    // Scoreboard to keep track of DUT FSM states
    scoreboard sc (.state(DUT.state));

    // Clock 
    localparam int PERIOD = 2, MAX_CYCLES = 1000000000;
    initial begin
        clk = 0; 
        repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
        $display ("\nA simulação atingiu o tempo limite. Terminando simulação.\n");
        $finish;
    end
    
    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(0, 6, "s", 11);

        $display("#==========================================================#");
        $monitor("%t: {LA,LB,LC,RA,RB,RC} = %b%b%b_%b%b%b. State is %s.", $realtime, LA, LB, LC, RA, RB, RC, DUT.state.name());

        // Driving stimulus
        reset();
        $display("Executing turn left sequence.");
        @(negedge clk) {LEFT, RIGHT, HAZ} = 3'b100;
        repeat (4) #(state_time*1s + PERIOD);
        $display("#==========================================================#");
        reset();
        $display("Executing turn right sequence.");
        @(negedge clk) {LEFT, RIGHT, HAZ} = 3'b010;
        repeat (4) #(state_time*1s + PERIOD);
        $display("#==========================================================#");
        reset();
        $display("Executing hazards sequence.");
        @(negedge clk) {LEFT, RIGHT, HAZ} = 3'b001;
        repeat (4) #(state_time*1s + PERIOD);
        $display("#==========================================================#");
        reset();
        $display("Executing random sequence.");
        repeat (10) begin
            @(negedge clk) assert(randomize(LEFT, RIGHT, HAZ) with {HAZ dist {1:=4, 0:=6}; {LEFT, RIGHT} dist {3:=4, [0:2]:=6};});
            $display("%t: {LEFT, RIGHT, HAZ} = %b%b%b", $realtime, LEFT, RIGHT, HAZ);
            repeat (5) #(state_time*1s + PERIOD);
        end 

        $display("#==========================================================#");
        $finish;
    end

    // Reset task
    task reset ();
        rst_n = 1;
        #1 rst_n = 0;
        #1 rst_n = 1;
        $display("%t: Reset done.", $realtime);
    endtask
    

endmodule