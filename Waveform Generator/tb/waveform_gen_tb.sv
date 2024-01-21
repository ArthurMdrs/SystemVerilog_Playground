
module waveform_gen_tb;

    // Specifying time units for the simulation
    timeunit 1ns;
    timeprecision 1ps;

    // Import packages
    import waveform_gen_pkg::*;

    // DUT parameters
    localparam int SEL_WIDTH = 8;

    // DUT signals
    logic signed [LUT_WIDTH-1:0] wave_o;
    logic                        clk;
    logic                        rst_n;
    logic        [SEL_WIDTH-1:0] freq_sel;
    wave_sel_t                   wave_sel; 
    logic                        halt;

    // The DUT
    waveform_gen #(
        .SEL_WIDTH(SEL_WIDTH)
    ) dut (
        .wave_o,
        .clk,
        .rst_n,
        .freq_sel,
        .wave_sel, 
        .halt
    );


    // Simulation variables
    real freq_o; // Actual output frequency
    real freq_xpct; // Expected output frequency
    real margin = 10; // Percentage margin of error allowed
    bit verbose = 1;
    int n_mismatches;
    
    // Frequency measurement variables
    bit got_peak, got_valley, up_n_down;
    bit signed [LUT_WIDTH-1:0] prev_sample;
    real peak_t, valley_t, prev_peak_t;
    bit wave_type_changed = 1;
    wave_sel_t prev_wave_type;
    bit [2:0] wave_type_cnt;

    // Input clock 
    localparam real FREQ_I = 1e9; // Hz
    localparam real PERIOD = 1 / FREQ_I * 1s; // simulation time units
    localparam int MAX_CYCLES = 10_000;
    initial begin
        clk = 0; 
        // repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
        forever #(PERIOD/2) clk = ~clk;
        $display ("\nSimulation reached the time limit. Terminating simulation.\n");
        $finish;
    end
    
    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(-9, 3, "ns", 10); // e.g.: " 900.000ns"

        $display("#==========================================================#");

        $display("Clock frequency is %.2e Hz.", FREQ_I);
        $display("The period is %.3f simulation time units.", PERIOD);
        
        reset ();

        halt = 0;
        // freq_sel = '1;
        freq_sel = 200;
        wave_sel = SINE_WAVE;
        prev_wave_type = wave_sel.next();

        repeat (50) @(negedge clk);

        // reset ();

        repeat (50) @(negedge clk);

        wave_sel = SAWTOOTH_WAVE;
        repeat (100) @(negedge clk);

        wave_sel = TRIANGULAR_WAVE;
        repeat (100) @(negedge clk);

        // TO DO: use the checkit task!!

        $display("%t: Simulation end. Number of mismatches: %0d.", $realtime, n_mismatches);

        $display("#==========================================================#");
        $finish;
    end

    // Monitor output frequency
    always @(wave_o) begin
        bit freq_valid;

        measure_freq ();

        freq_valid = got_peak;
        // freq_valid = (wave_sel == SAWTOOTH_WAVE) ? (got_peak) : (got_peak || got_valley);

        if (freq_valid) begin
            if (prev_wave_type != wave_sel)
                wave_type_changed = 1;
            else if (wave_type_changed)
                wave_type_cnt++;

            prev_wave_type = wave_sel;

            if (wave_type_cnt == 2) begin
                wave_type_changed = 0;
                wave_type_cnt = 0;
            end

            if (!wave_type_changed) begin
                freq_xpct = (FREQ_I * (freq_sel + 1) / 2.0**(SEL_WIDTH+1)) / (LUT_WIDTH/2);
                if (verbose) begin
                    $display("#==========================================================#");
                    $display("%t: Waveform type is %s.", $realtime, wave_sel.name());
                    $display("Measured frequency = %.2e. Expected frequency = %.2e.", freq_o, freq_xpct);
                    $display("#==========================================================#");
                end
            end

            // TO DO: use the checkit task!!
        end
    end

    //=============== Tasks and Functions - Begin ===============//

    task reset ();
        rst_n = 0;
        #3 rst_n = 1;
        $display("%t: Reset done.", $realtime);
    endtask

    task checkit (real expected, real actual, real margin);
        real abs_margin;

        assert (margin >= 0 && margin <= 100)
        else $display("Margin should be a valid percentage value!");

        abs_margin = expected * margin / 100;

        if (expected - actual > abs_margin || actual - expected > abs_margin) begin
            $display("%t: ERROR! Expected = %.2e. Actual = %.2e.", $realtime, expected, actual);
            n_mismatches++;
        end
    endtask

    task measure_freq ();
        if (wave_o > prev_sample) begin
            if (!up_n_down) begin
                got_valley = 1;
                valley_t = $realtime;
                got_peak = 0;
            end
            else begin
                got_valley = 0;
            end
            up_n_down = 1;
        end

        else if (wave_o < prev_sample) begin
            if (up_n_down) begin
                got_peak = 1;
                prev_peak_t = peak_t;
                peak_t = $realtime;
                got_valley = 0;
            end
            else begin
                got_peak = 0;
            end
            up_n_down = 0;
        end

        if (valley_t > 0 && peak_t > 0) begin
            if (wave_sel == SAWTOOTH_WAVE && got_peak) begin
                freq_o = 1s / (peak_t - prev_peak_t);
            end
            else begin
                if (got_peak)
                    freq_o = 1s / ((peak_t - valley_t) * 2);
                if (got_valley)
                    freq_o = 1s / ((valley_t - peak_t) * 2);
            end
        end

        prev_sample = wave_o;
    endtask

    task test_all_wave_types ();
        // TO DO!!
        // Should just be what's already being simulated
    endtask

    task test_different_freqs ();
        // TO DO!!
    endtask

    task test_different_duty_cycles ();
        // TO DO!!
    endtask


    // TO DO!! Function to calculate expected frequency!!
    
endmodule