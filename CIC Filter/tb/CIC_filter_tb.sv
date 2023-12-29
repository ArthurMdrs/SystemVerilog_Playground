module CIC_filter_tb;

    // DUT parameters
    localparam int WIDTH = 8;
    localparam int STAGES = 3;
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
        // $monitor("%t: {LA,LB,LC,RA,RB,RC} = %b%b%b_%b%b%b. State is %s.", $realtime, );
        input_file = $fopen("input.txt", "r");
        output_file = $fopen("output.txt", "w");

        // Driving stimulus
        reset();
        
        // Read and drive input data stream
        while (my_char !== 255) // 255 means End Of File
        begin        
            // Read next data input
            // errcode = $fscanf(input_file, "%d.%d", in, trash);
            errcode = $fscanf(input_file, "%d", in);
            
            // Gets newline or EOF
            my_char = $fgetc(input_file);
            
            if (my_char == 255)
                $display ("Reached input file end.");
            else
                $display("Input is %d", in);

            // Wait for inactive clock edge so the DUT sees input
            @(negedge clk);

            // Write output to file
            $fdisplay(output_file, "%d", out);
        end

        $fclose(input_file);
        $fclose(output_file);

        $display("#==========================================================#");
        $finish;
    end

endmodule