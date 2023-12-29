module CIC_filter_tb;

    // DUT parameters
    localparam int WIDTH = 8;
    localparam int STAGES = 1;
    localparam int RATE = 4;

    // DUT ports
    logic [WIDTH-1:0] out;
    logic [WIDTH-1:0] in;
    logic clk;
    logic rstn;

    // The DUT
    CIC_filter #(
        .WIDTH(WIDTH),
        .STAGES(STAGES),
        .RATE(RATE)
    ) CIC_filter_inst (
        .out,
        .in,
        .clk,
        .rstn
    );

    // Simulation variables
    int input_file, output_file, errcode, trash;
    byte my_char;
    int my_cnt;

    // Clock generation
    localparam int PERIOD = 2, MAX_CYCLES = 1000;
    initial begin
        clk = 0; 
        repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
        $display ("\nSimulation reached the time limit. Terminating simulation.\n");
        $finish;
    end

    // Reset task
    task reset ();
        rstn = 1;
        @(negedge clk) rstn = 0;
        @(negedge clk) rstn = 1;
        $display("%t: Reset done.", $realtime);
    endtask : reset
    
    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(-9, 0, " ns", 6);

        $display("#==========================================================#");
        input_file = $fopen("input.txt", "r");
        output_file = $fopen("output.txt", "w");

        // Driving stimulus
        reset();
        
        // Read and drive input data stream
        while (my_char !== 255) // 255 means End Of File
        begin        
            // Read next data input
            errcode = $fscanf(input_file, "%d", in);
            
            // Gets newline or EOF
            my_char = $fgetc(input_file);
            
            if (my_char == 255) begin
                $display ("Reached input file end.");
            end else begin
                $display("Input is %d", in);

                // Wait for inactive clock edge so the DUT sees input
                @(negedge clk);

                // foreach (CIC_filter_inst.integ_of_vec[i]) begin
                //     if (CIC_filter_inst.integ_of_vec[i])
                //         $display("%t OVERFLOW integ elem %d", $realtime, i);
                //     if (CIC_filter_inst.comb_of_vec[i])
                //         $display("%t OVERFLOW comb elem %d", $realtime, i);
                // end

                if (out == 0) 
                    my_cnt++;
                else
                    // Write output to file
                    // $display("Output is %d", out);
                    $fdisplay(output_file, "%d", out);
            end
        end

        while (my_cnt > 0) begin
            @(negedge clk);
            my_cnt--;
            $fdisplay(output_file, "%d", out);
        end

        $fclose(input_file);
        $fclose(output_file);

        $display("#==========================================================#");
        $finish;
    end

endmodule
