module ima_adpcm_decoder_tb;

// Specifying time units for the simulation
timeunit 1ns;
timeprecision 1ps;

// Import packages
// import ima_adpcm_decoder_pkg::*;

// DUT parameters

// DUT signals
    logic        clk;
    logic        rst_n;
    logic        sop;       // Start of packet
    logic        eop;       // End of packet
    logic [ 3:0] coded_i;   // Compressed (encoded) input data
    logic [15:0] decoded_o; // Decompressed (decoded) output data

// The DUT
ima_adpcm_decoder #(
) dut (
    .clk,
    .rst_n,
    .sop,      // Start of packet
    .eop,      // End of packet
    .coded_i,  // Compressed (encoded) input data
    .decoded_o // Decompressed (decoded) output data
);

// Simulation variables
int n_mismatches;
bit verbose = 0;
int max_samples = 1000;
bit [15:0] orig_data [];
bit [ 3:0] enc_data [];
bit [15:0] dec_data [];
bit [15:0] refmod_data [3];

// Clock 
localparam int PERIOD = 2;
localparam int MAX_CYCLES = 10_000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    // forever #(PERIOD/2) clk = ~clk;
    $display ("\nSimulation reached the time limit. Terminating simulation.\n");
    $finish;
end

// The proccess
initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 6); // e.g.: " 900ns"

    $display("#==========================================================#");
    
    read_file_16 ("audio_files/teste1_orig.wav", orig_data);
    read_file_4  ("audio_files/teste1_encod.wav", enc_data);
    read_file_16 ("audio_files/teste1_decod.wav", dec_data);
    // $display("Read: %p", enc_data);
    
    reset ();
    
    sop = 0;
    eop = 0;
    coded_i = '1;
    
    drive_pkt(enc_data);
    #20;
    
    // for (int i = 0; i < 20; i++) begin
    //     $display("%t: Expected = %0d. Actual = %0d.", $time, orig_data[i], actual);
    // end
    
    // $display("%t: Some value: %0d.", $time, dut.ima_step_table[87]);

    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

    $display("#==========================================================#");
    $finish;
end

//=============== Tasks and Functions - Begin ===============//

task reset ();
    rst_n = 1;
    @(negedge clk) rst_n = 0;
    @(negedge clk) rst_n = 1;
    $display("%t: Reset done.", $realtime);
endtask

task checkit (int expected, int actual);
    if (expected != actual) begin
        $display("%t: ERROR! Expected = %0d. Actual = %0d.", $time, expected, actual);
        n_mismatches++;
    end
endtask

task drive_pkt (bit [3:0] data []);
    int idx;

    if(data.size() == 0) begin
        $display("%t: ERROR! Attempted to drive empty array.", $time);
        $finish;
    end
    
    refmod_data = '{default:'0};
    
    @ (negedge clk) ;
    sop = 1;
    eop = 0;
    coded_i = data[0];
    refmod_data[0] = refmod(coded_i);
    
    for (int i = 1 ; i < data.size()-1 ; i++) begin
        @ (negedge clk) ;
        sop = 0;
        coded_i = data[i];
        refmod_data = {refmod(coded_i), refmod_data[0], refmod_data[1]};
        // if (idx < 20)
        //     $display("%t: Expected = %4h. Actual = %4h.", $time, orig_data[idx], decoded_o);
        // idx++;
        // if (i < 20)
        //     $display("%t: Expected = %4h. Actual = %4h.", $time, orig_data[i-1], decoded_o);
        if (refmod_data[2] != decoded_o) begin
            $display("%t: Refmod = %4h. Dut = %4h.", $time, refmod_data[2], decoded_o);
            $display("%t: Difference = %0d. ", $time, $signed(refmod_data[2] - decoded_o));
            // $display("%t: External decoder = %4h. ", $time, dec_data[i-1]);
            n_mismatches++;
        end
    end
    
    @ (negedge clk) ;
    eop = 1;
    coded_i = data[data.size()-1];
    refmod_data = {refmod(coded_i), refmod_data[0], refmod_data[1]};
    
    @ (negedge clk) ;
    eop = 0;
endtask

task automatic read_file_16 (string file_name, ref bit [15:0] dest []);
    int fp;
    bit [15:0] data_read [];
    int idx;
    byte my_char;
    bit toggle;
    
    fp = $fopen(file_name, "r");
    
    if (fp == 0) begin
        $display("Error opening the file");
        $finish;
    end
    
    while (!$feof(fp) && idx < max_samples) begin
        my_char = $fgetc(fp);
        if (!toggle) begin
            data_read = new [data_read.size()+1] (data_read);
            data_read[idx][7:0] = my_char;
        end
        else begin
            data_read[idx][15:8] = my_char;
            idx++;
        end
        toggle = !toggle;
    end
    
    $display("Size of data read from %s is %0d.", file_name, data_read.size());
    dest = data_read;
endtask

task automatic read_file_4 (string file_name, ref bit [3:0] dest []);
    int fp;
    bit [3:0] data_read [];
    int idx;
    byte my_char;
    
    fp = $fopen(file_name, "r");
    
    if (fp == 0) begin
        $display("Error opening the file");
        $finish;
    end
    
    while (!$feof(fp) && idx < max_samples) begin
        my_char = $fgetc(fp);
        data_read = new [data_read.size()+2] (data_read);
        data_read[idx] = my_char[3:0];
        idx++;
        data_read[idx] = my_char[7:4];
        idx++;
    end
    
    $display("Size of data read from %s is %0d.", file_name, data_read.size());
    dest = data_read;
endtask



//// REFERENCE MODEL
int ima_index_table [16] = '{
    -1, -1, -1, -1, 2, 4, 6, 8,
    -1, -1, -1, -1, 2, 4, 6, 8
};
int ima_step_table [89] = '{ 
        7,     8,     9,    10,    11,    12,    13,    14,    16,    17, 
       19,    21,    23,    25,    28,    31,    34,    37,    41,    45, 
       50,    55,    60,    66,    73,    80,    88,    97,   107,   118, 
      130,   143,   157,   173,   190,   209,   230,   253,   279,   307,
      337,   371,   408,   449,   494,   544,   598,   658,   724,   796,
      876,   963,  1060,  1166,  1282,  1411,  1552,  1707,  1878,  2066, 
     2272,  2499,  2749,  3024,  3327,  3660,  4026,  4428,  4871,  5358,
     5894,  6484,  7132,  7845,  8630,  9493, 10442, 11487, 12635, 13899, 
    15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767 
};
int predictor  = 0;
int step_index = 0;
int step       = ima_step_table[step_index];
function bit [15:0] refmod (bit [3:0] nibble);
    int diff, nibble_int;
    
    step_index = step_index + ima_index_table[nibble];
    if (step_index <  0) step_index = 0;
    if (step_index > 88) step_index = 88;
    nibble_int = (nibble[3]) ? (-nibble[2:0]) : (nibble[2:0]);
    diff = ((2*nibble_int + 1) * step) / 8;
    predictor = predictor + diff;
    if (predictor < -32768) predictor = -32768;
    if (predictor >  32767) predictor =  32767;
    step = ima_step_table[step_index];
    
    return predictor[15:0];
endfunction    

//=============== Tasks and Functions - End ===============//

endmodule