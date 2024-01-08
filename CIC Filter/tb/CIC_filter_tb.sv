typedef enum bit {FROM_TXT_FILE, FROM_RNG} input_mode_t;

module CIC_filter_tb;

    // DUT parameters
    // localparam int WIDTH = 8;
    // localparam int STAGES = 1;
    // localparam int RATE = 4;
    `include "params.sv"

    // DUT ports
    logic [WIDTH-1:0] out;
    logic [WIDTH-1:0] in;
    logic fast_clk;
    logic rstn;

    // The DUT
    CIC_filter #(
        .WIDTH(WIDTH),
        .STAGES(STAGES),
        .RATE(RATE),
        .DnI(DnI)
    ) CIC_filter_inst (
        .out,
        .in,
        .clk(fast_clk),
        .rstn
    );

    // Simulation parameters
    input_mode_t input_mode = FROM_TXT_FILE;
    int NUM_TRANS = 500;
    bit verbose = 1;

    // Simulation variables
    int input_file, output_file, errcode;
    byte my_char;
    int out_cnt, expected_latency;
    bit out_cnt_flag;
    int last_samples [RATE];
    int last_sum, accum, last_avg;
    logic [$clog2(RATE)-1:0] cnt_to_size = 0;

    // Clock generation
    localparam int PERIOD = 2, MAX_CYCLES = 10000;
    // bit fast_clk;
    initial begin
        fast_clk = 0; 
        repeat(MAX_CYCLES) #(PERIOD/2) fast_clk = ~fast_clk;
        $display ("\nSimulation reached the time limit. Terminating simulation.\n");
        $finish;
    end

    bit slow_clk; // Used to drive input for interpolator
    // initial begin
    //     slow_clk = 0;
    //     forever
    //         #(RATE*PERIOD/2) slow_clk = ~slow_clk;
    // end

    logic [$clog2(RATE/2):0] cnt;
    always_ff @(posedge fast_clk or negedge rstn) begin
        if (!rstn) begin
            cnt <= 0;
            slow_clk <= 0;
        end else if (cnt < RATE/2 - 1) begin
            cnt <= cnt + 1;
        end else begin
            cnt <= 0;
            slow_clk <= !slow_clk;
        end
    end

    // ===================== TASKS AND FUNCTIONS BEGIN ===================== //
    task reset ();
        rstn = 1;
        @(negedge fast_clk) rstn = 0;
        @(negedge fast_clk) rstn = 1;
        $display("%t: Reset done.", $realtime);
    endtask : reset

    function int compute_expected_latency (int stages); // Ignore this
        int cnt_down;
        int expected_latency;

        cnt_down = stages;
        expected_latency = 5;
        while (cnt_down > 1) begin
            if (cnt_down % 2 == 0)
                expected_latency += 8;
            else
                expected_latency += 4;
            cnt_down--;
        end
            // $display("value is %0d", expected_latency);
        return expected_latency;
    endfunction : compute_expected_latency

    function void update_debug_vars ();
        if (RATE > 1)
            last_samples[1:RATE-1] = last_samples[0:RATE-2];
        last_samples[0] = in;

        last_sum = 0;
        foreach (last_samples[i])
            last_sum += last_samples[i];

        accum += in;

        // last_avg = last_sum / RATE;
        last_avg = last_sum >> $clog2(RATE);
    endfunction : update_debug_vars

    task automatic checkit (int expected, bit verbose = 0);
        repeat (expected_latency)
            @(negedge fast_clk);
        if (out == expected || expected - out == 1 || out - expected == 1) begin
            if (verbose) 
                $display("%t: Pass. Expected = %3d, out = %3d.", $realtime, expected, out);
        end else begin
            $display("%t: ERROR! Expected = %3d, out = %3d.", $realtime, expected, out);
        end
        // $display("%t: expected = %0d, out = %0d.", $realtime, expected, out);
    endtask : checkit
    // ====================== TASKS AND FUNCTIONS END ====================== //
    
    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(-9, 0, " ns", 6);

        $display("#==========================================================#");

        if (verbose) begin
            $display("Parameter WIDTH is %0d", WIDTH);
            $display("Parameter STAGES is %0d", STAGES);
            $display("Parameter RATE is %0d", RATE);
        end

        // Compute expected latency between full set of inputs and corresponding output
        expected_latency = compute_expected_latency(STAGES);

        // Driving stimulus
        reset();

        if (input_mode == FROM_TXT_FILE) begin
            // Open files
            input_file = $fopen("input.txt", "r");
            output_file = $fopen("output.txt", "w");

            // Read and drive input data stream
            while (my_char !== 255) begin
                // Read next data input
                // if (DnI) begin
                //     errcode = $fscanf(input_file, "%d", in);
                // end else if (cnt_to_size == 0) begin
                //     errcode = $fscanf(input_file, "%d", in);
                //     $display("%t: in is %0d", $time, in);
                // end
                if (DnI || cnt_to_size == 0) begin
                    errcode = $fscanf(input_file, "%d", in);
                    // $display("%t: in is %0d", $time, in);
                    
                    // Gets newline or EOF
                    my_char = $fgetc(input_file);
                end
                
                update_debug_vars();

                // Wait for inactive clock edge so the DUT sees input
                @(negedge fast_clk);

                // Keep counting until we see the output changes
                if (out == 0 && !out_cnt_flag) 
                    out_cnt++;
                else
                    out_cnt_flag = 1;

                // Perform checking
                // if (cnt_to_size == 0)
                //     fork
                //         checkit (last_avg, verbose);
                //     join_none

                cnt_to_size++;

                // Write output to file
                $fdisplay(output_file, "%d", out);
                // $display("Output is %d", out);
            end
            // $display("%t: Output starts updating after %0d clks.", $realtime, out_cnt);

            // Keep observing outputs
            while (out_cnt > 0) begin
                @(negedge fast_clk);
                out_cnt--;
                $fdisplay(output_file, "%d", out);
            end

            // Close files
            $fclose(input_file);
            $fclose(output_file);
        end



        else if (input_mode == FROM_RNG) begin
            // Open files
            input_file = $fopen("input.txt", "w");
            output_file = $fopen("output.txt", "w");

            repeat (NUM_TRANS * RATE) begin
                // Generate a randomized input
                assert(randomize(in));
                
                update_debug_vars();

                // Wait for inactive clock edge so the DUT sees input
                @(negedge fast_clk);

                // Keep counting until we see the output changes
                if (out == 0 && !out_cnt_flag) 
                    out_cnt++;
                else
                    out_cnt_flag = 1;

                // Write to files
                $fdisplay(input_file, "%d", in);
                $fdisplay(output_file, "%d", out);
            end
            
            // Keep observing outputs
            while (out_cnt > 0) begin
                @(negedge fast_clk);
                out_cnt--;
                $fdisplay(output_file, "%d", out);
            end

            // Close files
            $fclose(input_file);
            $fclose(output_file);
        end

        $display("#==========================================================#");
        $finish;
    end

    // int cnt1, cnt2;
    // always @(posedge fast_clk) $display("%t: f %0d", $time, cnt1++);
    // always @(posedge slow_clk) $display("%t: s %0d", $time, cnt2++);
    // final $display("f %0d s %0d", cnt1, cnt2);
    // final $display("fp %0d", PERIOD/2);
    // final $display("sp %0d", RATE*PERIOD/2);

    // Write output file
    // initial begin
    //     output_file = $fopen("output.txt", "w");

    //     repeat (2) // wait reset
    //         @(negedge input_clk);
        
    //     // Wait for inactive clock edge so we know output was driven
    //     @(negedge output_clk);
        
    // end

endmodule




                // foreach (CIC_filter_inst.integ_of_vec[i]) begin
                //     if (CIC_filter_inst.integ_of_vec[i])
                //         $display("%t OVERFLOW integ elem %d", $realtime, i);
                //     if (CIC_filter_inst.comb_of_vec[i])
                //         $display("%t OVERFLOW comb elem %d", $realtime, i);
                // end