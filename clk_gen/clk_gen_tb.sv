module clk_gen_tb;

    // Specifying time units for the simulation
    timeunit 1ns;
    timeprecision 1ps;

    // DUT parameters
    localparam int SEL_WIDTH = 5;

    // DUT signals
    logic                 clk_o;
    logic                 clk_i;
    logic [SEL_WIDTH-1:0] freq_sel;
    logic                 halt;
    logic                 rst_n;

    // The DUT
    clk_gen #(
        .SEL_WIDTH(SEL_WIDTH)
    ) dut (
        .clk_o,
        .clk_i,
        .freq_sel,
        .halt,
        .rst_n
    );

    // Simulation variables
    real t_wdw_start, t_wdw_end;
    int wdw_n_periods = 3;
    real freq_o;
    real freq_xpct;

    // Input clock 
    localparam real FREQ_I = 600e6; // Hz
    localparam real PERIOD = 1 / FREQ_I * 1s; // simulation time units
    localparam int MAX_CYCLES = 10000;
    initial begin
        clk_i = 0; 
        repeat(MAX_CYCLES) #(PERIOD/2) clk_i = ~clk_i;
        $display ("\nSimulation reached the time limit. Terminating simulation.\n");
        $finish;
    end
    
    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(-9, 3, "ns", 10); // e.g.: " 900.000ns"

        $display("#==========================================================#");

        $display("Original frequency is %.2e Hz.", FREQ_I);
        $display("Original period is %.3e s.", 1 / FREQ_I);
        $display("Original period is %.3f simulation time units.", PERIOD);
        
        reset ();

        halt = 0;
        freq_sel = 0;

        // Let each input value hold for a time window
        // and calculate the average output frequency
        do begin
            wdw_n_periods = freq_sel + 2;
            t_wdw_start = $realtime;
            repeat(wdw_n_periods) @(negedge clk_o);
            t_wdw_end = $realtime;
            freq_o = 1s / ((t_wdw_end - t_wdw_start) / wdw_n_periods);

            freq_xpct = FREQ_I * (freq_sel + 1) / 2.0**(SEL_WIDTH+1);
            print_vals ();

            freq_sel += 1;
        end while (freq_sel != '0);

        $display("#==========================================================#");
        $finish;
    end

    //=============== Tasks and Functions - Begin ===============//

    // Reset task
    task reset ();
        rst_n = 0;
        #3 rst_n = 1;
        $display("%t: Reset done.", $realtime);
    endtask

    task print_vals ();
        $display("%t: Freq sel = 0x%h. Output freq = %.2e. Expected freq = %.2e.", $realtime, freq_sel, freq_o, freq_xpct);
    endtask

endmodule