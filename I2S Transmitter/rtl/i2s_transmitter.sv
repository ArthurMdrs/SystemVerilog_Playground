module i2s_transmitter #(
    int DWIDTH = 8
) (
    output logic                ready,
    input  logic                clk,
    input  logic                rst_n,
    input  logic [2*DWIDTH-1:0] tx_data,

    // I2S interface - begin
    output logic SCLK,  // bit clock
    output logic WS,    // word select
    output logic SD     // serial data
    // I2S interface - end
);

typedef enum logic {IDLE, TRANSMIT} state_t;
state_t state;

localparam int BIT_CNT_WID = $clog2(2*DWIDTH);
logic [BIT_CNT_WID-1:0] bit_cnt; // Counter of bits transmitted
logic [2*DWIDTH-1:0] tx_data_buffer; // Buffer for data to be transmitted

// Update state
always_ff @(posedge clk) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= TRANSMIT;
end

// Drive ready signal
always_comb begin
    case (state)
        default : ready = 0;
        IDLE    : ready = 1;
        TRANSMIT: ready = (bit_cnt == 2*DWIDTH-1);
    endcase
end

// Bit counter and buffer the transmit data
always_ff @(posedge clk) begin
    if (!rst_n) begin
        bit_cnt <= '0;
        tx_data_buffer <= '0;
    end
    else begin
        if (ready)
            bit_cnt <= '0;
        else if (state == TRANSMIT) 
            bit_cnt <= bit_cnt + 1;
        tx_data_buffer <= (ready) ? (tx_data) : (tx_data_buffer << 1);
    end
end

// Create a delayed reset to turn off SCLK after the first cycle of a reset
// Because that would be (theoretically) the LSB of the previous Tx data
logic delayed_rst_n;
always_ff @(posedge clk) begin
    if (!rst_n) 
        delayed_rst_n <= 0;
    else if (state == TRANSMIT)
        delayed_rst_n <= 1;
end



// Drive I2S interface signals

// Bit clock is turned off during reset (and one cycle after)
assign SCLK = (!delayed_rst_n) ? 0 : clk;

// Drive Serial Data and Word Select on the falling edge of the clock
always_ff @(negedge clk) begin
    if (!rst_n) begin
        SD <= 0;
        WS <= 0;
    end else begin 
        SD <= tx_data_buffer[2*DWIDTH-1]; // Serial data is the MSB of the data buffer
        WS <= (bit_cnt inside {[DWIDTH-1 : 2*DWIDTH-2]}); // Word select is 0 for the 1st word and 1 for the 2nd
        // WS <= !(bit_cnt inside {[0 : DWIDTH], 2*DWIDTH-1}); // Word select is 0 for the 1st word and 1 for the 2nd
    end
end

endmodule
