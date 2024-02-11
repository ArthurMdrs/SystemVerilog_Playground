module spdif_aes3_transmitter_tb;

// Specifying time units for the simulation
timeunit 1ns;
timeprecision 1ps;

// Import packages
import spdif_aes3_transmitter_pkg::*;

// DUT parameters
localparam int SAMPLE_WIDTH = 24;

// DUT signals
logic clk;
logic rst_n;
logic halt;
logic [2*SAMPLE_WIDTH-1:0] sample_i;
logic tx_o;
logic ready;

// The DUT
spdif_aes3_transmitter #(
    .SAMPLE_WIDTH(SAMPLE_WIDTH)
) dut (
    .clk,
    .rst_n,
    .halt,
    .sample_i,
    .tx_o,
    .ready
);

// Simulation variables
int n_mismatches;
bit verbose = 1;
int block_cycles = 192*32*2*2;
int audio_blk_idx;
int chk_idx;
int parity_cnt;

typedef logic [0:191] [2*SAMPLE_WIDTH-1:0] audio_block_t;
audio_block_t audio_block;

// Clock 
localparam int PERIOD = 2;
localparam int MAX_CYCLES = 10_000;
initial begin
    clk = 0; 
    // repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    forever #(PERIOD/2) clk = ~clk;
    $display ("Simulation reached the time limit. Terminating simulation.");
    $finish;
end

// Decoded information
localparam int DEC_CLK_PERIOD = 2*PERIOD;
logic dec_clk, dec_data, dec_vld, dec_usr, dec_ch, dec_par;
logic tx_o_valid;
logic [47:0] dec_sample;

// The proccess
initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 7); // e.g.: "  900ns"

    $display("#==========================================================#");
    
    reset ();

    halt = 0;
    dec_clk = 0;
    dec_data = 0;
    dec_sample = '0;

    assert (randomize (audio_block));

    fork
    // Drive the input data sample
    repeat(block_cycles) begin
        if (ready) begin
            sample_i = audio_block[audio_blk_idx];
            audio_blk_idx++;
        end
        if (audio_blk_idx == 192)
            audio_blk_idx = 0;
        @(negedge clk);
    end
    // Read the output data stream and check it
    repeat(192+1) begin
        detect_preamble(); // Subframe 1
        read_data();
        check_parity();
        detect_preamble(); // Subframe 2
        read_data();
        check_parity();
        checkit(audio_block[chk_idx], dec_sample);
        chk_idx++;
    end
    join    

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

task checkit (logic [2*SAMPLE_WIDTH-1:0] expected, logic [47:0] actual);
    logic [47:0] exp_;

    case (SAMPLE_WIDTH)
        16: exp_ = {4'd0, expected[31:16], 8'd0, expected[15:0], 4'd0};
        20: exp_ = {expected[39:20], 4'd0, expected[19:0], 4'd0};
        24: exp_ = expected;
        default: $display("INVALID SAMPLE WIDTH!");
    endcase

    if (actual != exp_) begin
        $display("%t: ERROR! Expected = %0h. Actual = %0h.", $time, expected, exp_);
        n_mismatches++;
    end
endtask

task detect_preamble;
    preamble_t preamble_read;
    logic [7:0] aux;
    logic got_preamble;

    aux = '0;
    preamble_read = RESET;
    got_preamble = 0;
    while (!got_preamble) begin
        @(negedge clk);
        aux = {tx_o, aux[7:1]};
        if (aux inside {PREAMBLE_Z_0, PREAMBLE_Z_1, 
                        PREAMBLE_Y_0, PREAMBLE_Y_1, 
                        PREAMBLE_X_0, PREAMBLE_X_1}) 
        begin
            preamble_read = preamble_t'(aux);
            got_preamble = 1;
        end
    end
    if (verbose)
        $display("%t: Got preamble %s.", $time, preamble_read.name());
endtask

task read_data;
logic temp;

fork
    begin // Generate decoded clock 
        repeat(2) @(negedge clk);
        dec_clk = 1;
        repeat(24*2) 
            #(DEC_CLK_PERIOD/2) dec_clk = !dec_clk;
        dec_clk = 0;
    end

    begin // Decode output data
        tx_o_valid = 0; // This is a debug signal
        parity_cnt = 0;
        repeat(24) begin// Decode audio data
            @(negedge clk) temp = tx_o;
            @(negedge clk) dec_data = (tx_o != temp);
            dec_sample = {dec_data, dec_sample[47:1]};
            parity_cnt = parity_cnt + dec_data;
            tx_o_valid = 1;
        end
        // dec_vld, dec_usr, dec_ch, dec_par
        // Decode validity bit
        @(negedge clk) temp = tx_o;
        @(negedge clk) dec_vld = (tx_o != temp);
        parity_cnt = parity_cnt + dec_vld;
        tx_o_valid = 0;
        // Decode user bit
        @(negedge clk) temp = tx_o;
        @(negedge clk) dec_usr = (tx_o != temp);
        parity_cnt = parity_cnt + dec_usr;
        // Decode channel status bit
        @(negedge clk) temp = tx_o;
        @(negedge clk) dec_ch = (tx_o != temp);
        parity_cnt = parity_cnt + dec_ch;
        // Decode parity bit
        @(negedge clk) temp = tx_o;
        @(negedge clk) dec_par = (tx_o != temp);
        parity_cnt = parity_cnt + dec_par;
    end
join
endtask

task check_parity ();
    // if (parity_cnt[0] != 1'b0) begin
    if (parity_cnt % 2 == 1'b1) begin
        $display("%t: PARITY ERROR.", $realtime);
        n_mismatches++;
    end
endtask

//=============== Tasks and Functions - End ===============//

endmodule

