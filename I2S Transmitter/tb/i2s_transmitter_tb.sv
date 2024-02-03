module i2s_transmitter_tb;

// Specifying time units for the simulation
timeunit 1ns;
timeprecision 1ps;

// DUT parameters
localparam int DWIDTH = 8;

// DUT signals
logic                ready;
logic                clk;
logic                rst_n;
logic [2*DWIDTH-1:0] tx_data;

// I2S interface - begin
logic SCLK;  // bit clock
logic WS;    // word select
logic SD;    // serial data
// I2S interface - end

// The DUT
i2s_transmitter #(
    .DWIDTH(DWIDTH)
) dut (
    .ready,
    .clk,
    .rst_n,
    .tx_data,
    .SCLK,
    .WS,
    .SD
);

// Simulation variables
int n_mismatches;
logic [2*DWIDTH-1:0] data_mem [64];
int send_idx, recv_idx;
logic [2*DWIDTH-1:0] rcv_data;    // Recovered data
logic [2*DWIDTH-1:0] n_rcv_data;  // Next value of recovered data

// Clock 
localparam int PERIOD = 2;
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
    $timeformat(-9, 0, "ns", 6); // e.g.: " 900ns"

    $display("#==========================================================#");
    
    reset ();
    assert(randomize(data_mem));

    repeat(20) begin
        tx_data = data_mem[send_idx];
        send_idx++;
        @(posedge ready);
    end

    reset ();
    recv_idx++;

    while(send_idx <= 63) begin
        tx_data = data_mem[send_idx];
        send_idx++;
        @(posedge ready);
    end

    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

    $display("#==========================================================#");
    $finish;
end

// Update value of received data
always_ff @(posedge SCLK) begin
    if(!rst_n)
        n_rcv_data <= '0;
    else 
        n_rcv_data <= {n_rcv_data, SD};
end

// When WS goes low (except on reset), wait 1 more cycle until
// we get the entire 2 data words. Then print them
always @(negedge WS iff (rst_n)) begin
    @(negedge SCLK);
    rcv_data = n_rcv_data;
    checkit(data_mem[recv_idx], rcv_data);
    recv_idx++;
    $display("%t: Transmitted following data: %h. Index = %0d", $time, rcv_data, recv_idx);
end

//=============== Tasks and Functions - Begin ===============//

task reset ();
    rst_n = 0;
    #3 rst_n = 1;
    $display("%t: Reset done.", $realtime);
endtask

task checkit (int expected, int actual);
    if (expected != actual) begin
        $display("%t: ERROR! Expected = %4h. Actual = %4h.", $time, expected, actual);
        n_mismatches++;
    end
endtask

//=============== Tasks and Functions - End ===============//

endmodule
