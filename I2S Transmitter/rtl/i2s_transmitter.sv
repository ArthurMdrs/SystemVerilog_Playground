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

import i2s_transmitter_pkg::*;

state_t state, n_state; // State and next state

localparam int BIT_CNT_WID = $clog2(2*DWIDTH);
logic [BIT_CNT_WID-1:0] bit_cnt; // Counter of bits transmitted
logic [2*DWIDTH-1:0] tx_data_buffer; // Buffer for data to be transmitted

logic SCLK_en; // Enable for SCLK



// FSM update state logic
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= n_state;
end

// FSM next state logic
always_comb begin
    case (state)
        default : n_state = state.next();
        TRANSMIT: n_state = (bit_cnt < 2*DWIDTH-1) ? TRANSMIT : LOAD;
    endcase
end

// FSM output logic
always_comb begin
    case (state)
        default : ;
        IDLE    : {ready, SCLK_en} = 2'b10;
        LOAD    : {ready, SCLK_en} = 2'b00;
        TRANSMIT: begin
            ready = (bit_cnt == 2*DWIDTH-1);
            SCLK_en = 1'b1;
        end
    endcase
end

// Bit counter and buffer the transmit data
always_ff @(posedge clk or negedge rst_n) begin
// always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n) begin
        bit_cnt <= '0;
        tx_data_buffer <= '0;
    end
    else begin
        if (state == LOAD) 
            bit_cnt <= '0;
        else if (state == TRANSMIT) 
            bit_cnt <= bit_cnt + 1;
        tx_data_buffer <= (state == LOAD) ? (tx_data) : (tx_data_buffer << 1);
    end
end

// Drive I2S interface signals
assign SCLK = clk && SCLK_en;
assign WS = bit_cnt[BIT_CNT_WID-1];
always_comb begin
    if (state == TRANSMIT)
        SD = tx_data_buffer[2*DWIDTH-1];
    else
        SD = '0;
end

endmodule
