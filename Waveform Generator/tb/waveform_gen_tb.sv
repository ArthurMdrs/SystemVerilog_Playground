
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
    logic                        saw_reverse;
    logic        [CNT_WIDTH-1:0] rec_duty_cyc;

    // The DUT
    waveform_gen #(
        .SEL_WIDTH(SEL_WIDTH)
    ) dut (
        .wave_o,
        .clk,
        .rst_n,
        .freq_sel,
        .wave_sel, 
        .halt,
        .saw_reverse,
        .rec_duty_cyc
    );


    // Simulation variables
    real freq_o; // Actual output frequency
    real freq_xpct; // Expected output frequency
    real margin = 10; // Percentage margin of error allowed
    bit verbose = 0;
    int n_mismatches;
    enum {ALL_WAVE_TYPES, DIFF_FREQS, RECT_DUTY_CYCLE, SAW_REVERSE, HALT} test_sel;
    
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
        saw_reverse = 1;
        rec_duty_cyc = 0.7 * (2**CNT_WIDTH-1);
        freq_sel = 200;
        wave_sel = SINE_WAVE;
        prev_wave_type = wave_sel.next();

        test_sel = DIFF_FREQS;

        case (test_sel)
            ALL_WAVE_TYPES: 
                test_all_wave_types (get_expected_freq ());
            DIFF_FREQS: // We get frequency errors in this, but graphically seems fine
                test_different_freqs (TRIANGULAR_WAVE);
            RECT_DUTY_CYCLE: 
                test_different_duty_cycles (get_expected_freq ());
            SAW_REVERSE:
                test_saw_reverse(get_expected_freq ());
            HALT: // We can expect to get frequency errors in this
                test_halt(get_expected_freq ());
        endcase

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
                freq_xpct = get_expected_freq();
                if (verbose) begin
                    $display("#==========================================================#");
                    $display("%t: Waveform type is %s.", $realtime, wave_sel.name());
                    $display("Measured frequency = %.2e. Expected frequency = %.2e.", freq_o, freq_xpct);
                    $display("#==========================================================#");
                end
                checkit (freq_xpct, freq_o, margin);
            end

        end
    end

    //=============== Tasks and Functions - Begin ===============//

    task reset ();
        rst_n = 1;
        @(negedge clk) rst_n = 0;
        @(negedge clk) rst_n = 1;
        $display("%t: Reset done.", $realtime);
    endtask

    task checkit (real expected, real actual, real margin);
        real abs_margin;

        assert (margin >= 0 && margin <= 100)
        else $display("Margin should be a valid percentage value!");

        abs_margin = expected * margin / 100;

        if (expected - actual > abs_margin || actual - expected > abs_margin) begin
            $display("%t: ERROR! Expected = %.2e. Actual = %.2e. Wave type = %s.", $realtime, expected, actual, wave_sel.name());
            n_mismatches++;
        end
    endtask

    task measure_freq ();
        if (wave_sel == RECTANGULAR_WAVE) begin
            if (!got_peak && wave_o > 0) begin
                got_peak = 1;
                freq_o = 1s / ($realtime - peak_t);
                peak_t = $realtime;
            end
            else if (wave_o < 0) begin
                got_peak = 0;
            end
        end
        else begin
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
        end
    endtask

    task test_all_wave_types (real freq);
        real rpt_cycles;
        wave_sel_t t;
        rpt_cycles = 2s / freq; // This is 2x expected Period

        halt = 0;
        saw_reverse = 0;
        rec_duty_cyc = 0.5* (2**CNT_WIDTH-1);
        prev_wave_type = wave_sel.last();

        t = t.first();
        do begin
            wave_sel = t;
            repeat (rpt_cycles) @(negedge clk);
            t = t.next();
        end while (t != t.first());

    endtask

    task test_different_freqs (wave_sel_t wave_type);
        real rpt_cycles;
        wave_sel = wave_type;

        halt = 0;
        saw_reverse = 0;
        rec_duty_cyc = 0.3 * (2**CNT_WIDTH-1);
        prev_wave_type = wave_sel.next();

        for (int i = 0; i < 2**SEL_WIDTH; i++) begin
            freq_sel = i;
            rpt_cycles = 2s / get_expected_freq (); // This is 2x expected Period
            repeat (rpt_cycles) @(negedge clk);
        end
    endtask

    task test_different_duty_cycles (real freq);
        real rpt_cycles;
        rpt_cycles = 3s / freq; // This is 3x expected Period

        halt = 0;
        wave_sel = RECTANGULAR_WAVE;
        prev_wave_type = wave_sel.next();

        for (int i = 0; i < 2**CNT_WIDTH; i++) begin
            rec_duty_cyc = i;
            repeat (rpt_cycles) @(negedge clk);
        end
    endtask

    task test_saw_reverse (real freq);
        real rpt_cycles;
        rpt_cycles = 2s / freq; // This is 2x expected Period

        halt = 0;
        saw_reverse = 0;
        freq_sel = 255;
        wave_sel = SAWTOOTH_WAVE;
        prev_wave_type = wave_sel.next();

        repeat (rpt_cycles) @(negedge clk);

        saw_reverse = 1;
        
        repeat (rpt_cycles) @(negedge clk);
    endtask

    task test_halt (real freq);
        real rpt_cycles;
        rpt_cycles = 3s / freq; // This is 3x expected Period

        halt = 0;
        saw_reverse = 0;
        freq_sel = 255;
        wave_sel = SAWTOOTH_WAVE;
        prev_wave_type = wave_sel.next();

        repeat (rpt_cycles/2) @(negedge clk);
        halt = 1;
        repeat (rpt_cycles/4) @(negedge clk);
        halt = 0;
        repeat (rpt_cycles/4) @(negedge clk);

        saw_reverse = 1;
        
        halt = 1;
        repeat (rpt_cycles/4) @(negedge clk);
        halt = 0;
        repeat (rpt_cycles/4) @(negedge clk);
        halt = 1;
        repeat (rpt_cycles/4) @(negedge clk);
        halt = 0;
        repeat (rpt_cycles/4) @(negedge clk);

    endtask

    function real get_expected_freq ();
        return (FREQ_I * (freq_sel + 1) / 2.0**(SEL_WIDTH+1)) / (LUT_SIZE/2);
    endfunction

    //=============== Tasks and Functions - End ===============//
    
endmodule