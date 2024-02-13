module spdif_aes3_transmitter #(
    parameter int SAMPLE_WIDTH = 16
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic                      halt,
    input  logic [2*SAMPLE_WIDTH-1:0] sample_i,
    output logic                      tx_o,
    output logic                      ready
);

import spdif_aes3_transmitter_pkg::*;

// Registers 
logic [23:0] audio_data_L;  // Maximum of 24 bits of audio data in a subframe
logic [23:0] audio_data_R;  // Maximum of 24 bits of audio data in a subframe
logic [ 8:0] subframe_cnt;  // Counter of subframes transmitted
logic [ 5:0] bit_cnt;       // Counter of bits transmitted in the current frame
logic [ 5:0] parity_cnt;    // Counter of 1's in the subframe
logic        force_toggle;  // Force transition for Manchester Encoding
logic        parity;        // Value should make bits 4-31 have even no. of 1's
logic        ch_bit;        // Channel status bit

logic [SAMPLE_WIDTH-1:0] sample_buffer_L; // Left (or A) channel sample
logic [SAMPLE_WIDTH-1:0] sample_buffer_R; // Right (or B) channel sample
subframe_t subframe_which;  // Subframe is left or right?
preamble_t preamble;        // See related SV package

// Next audio bit to be transmitted
wire next_L = audio_data_L[(bit_cnt - 8) / 2];
wire next_R = audio_data_R[(bit_cnt - 8) / 2];

////////////////////////////////
////    SUBFRAME COUNTER    ////
////////////////////////////////
// There are 192 frames in an audio block
// 192 x 2 = 384 subframes
always_ff @(posedge clk) begin
    if(!rst_n) begin
        subframe_cnt <= 383;
        subframe_which <= RIGHT;
    end
    else if (!halt && bit_cnt == 63) begin
        if (subframe_cnt == 383) // 384 subframes in an audio block
            subframe_cnt <= '0;
        else
            subframe_cnt <= subframe_cnt + 9'd1;
        
        // subframe_which <= !subframe_which; // Change from left to right and vice-versa
        subframe_which <= subframe_which.next(); // Same as line above
    end
end

///////////////////////////
////    BIT COUNTER    ////
///////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        bit_cnt <= '1;
        ready <= 1'b1;
    end
    else if (!halt) begin
        if (bit_cnt == 63) begin // 32 timeslots for each channel = 64 timeslots
            bit_cnt <= '0;
            ready <= 1'b0;
        end else begin
            bit_cnt <= bit_cnt + 6'd1;
            if (bit_cnt == 62 && subframe_which == RIGHT)
                ready <= 1'b1;
        end
    end
    else
        ready <= 1'b0;
end

///////////////////////////////////////
////    BUFFER THE INPUT SAMPLE    ////
///////////////////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        sample_buffer_L <= '0;
        sample_buffer_R <= '0;
    end
    else if (!halt && ready) begin
        sample_buffer_L <= sample_i[  SAMPLE_WIDTH-1:           0];
        sample_buffer_R <= sample_i[2*SAMPLE_WIDTH-1:SAMPLE_WIDTH];
    end
end

//////////////////////////////////////
////    DETERMINE THE PREAMBLE    ////
//////////////////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        preamble <= RESET;
    end
    else if (!halt && bit_cnt == 63) begin
    if (subframe_cnt == 383)            // Start of audio block (preamble Z)
        if (parity == 1'b1)
            preamble <= (tx_o) ? PREAMBLE_Z_0 : PREAMBLE_Z_1;
        else
            preamble <= (tx_o) ? PREAMBLE_Z_1 : PREAMBLE_Z_0;
    else if (subframe_cnt[0] == 1'b1)   // Left channel (or A channel)
        if (parity == 1'b1)
            preamble <= (tx_o) ? PREAMBLE_X_0 : PREAMBLE_X_1;
        else
            preamble <= (tx_o) ? PREAMBLE_X_1 : PREAMBLE_X_0;
    else                                // Right channel (or B channel)
        if (parity == 1'b1)
            preamble <= (tx_o) ? PREAMBLE_Y_0 : PREAMBLE_Y_1;
        else
            preamble <= (tx_o) ? PREAMBLE_Y_1 : PREAMBLE_Y_0;
    end
end

/////////////////////////////////////
////    DRIVE AUDIO DATA BITS    ////
/////////////////////////////////////
always_comb begin
    if (SAMPLE_WIDTH == 16) begin
        audio_data_L = {4'd0, sample_buffer_L, 4'd0};
        audio_data_R = {4'd0, sample_buffer_R, 4'd0};
    end
    else if (SAMPLE_WIDTH == 20) begin
        audio_data_L = {sample_buffer_L, 4'd0};
        audio_data_R = {sample_buffer_R, 4'd0};
    end
    else if (SAMPLE_WIDTH == 24) begin
        audio_data_L = sample_buffer_L;
        audio_data_R = sample_buffer_R;
    end
end

///////////////////////////////////////
////    FORCE TRANSITION SIGNAL    ////
///////////////////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        force_toggle <= 1'b0;
    end
    else if (!halt) begin
        force_toggle <= !force_toggle;
    end
end

//////////////////////////
////    OUTPUT BIT    ////
//////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        tx_o <= 1'b0;
    end
    else if (!halt) begin
        if (bit_cnt < 8) begin // We are in the preamble
            tx_o <= preamble[bit_cnt[2:0]];
        end
        else if (bit_cnt < 56) begin // We are in the audio data region
            if (force_toggle)
                tx_o <= !tx_o;
            else if (subframe_which == LEFT && next_L == 1'b1)
                tx_o <= !tx_o;
            else if (subframe_which == RIGHT && next_R == 1'b1)
                tx_o <= !tx_o;
            else
                tx_o <=  tx_o;
        end
        else if (bit_cnt < 58) begin // This is the valid bit (always 0)
            tx_o <= (force_toggle) ? !tx_o : tx_o;
        end
        else if (bit_cnt < 60) begin // This is the user data bit (always 0)
            tx_o <= (force_toggle) ? !tx_o : tx_o;
        end
        else if (bit_cnt < 62) begin // This is the channel status bit
            if (force_toggle)
                tx_o <= !tx_o;
            else if (ch_bit)
                tx_o <= !tx_o;
        end
        else begin                   // This is the parity bit
            if (force_toggle)
                tx_o <= !tx_o;
            else if (parity)
                tx_o <= !tx_o;
        end
    end
end

//////////////////////////
////    PARITY BIT    ////
//////////////////////////
always_ff @(posedge clk) begin
    if(!rst_n) begin
        parity_cnt <= '0;
    end
    else if (!halt) begin
        if (bit_cnt < 8) begin // We are in the preamble
            parity_cnt <= '0;
        end
        else if (bit_cnt < 56) begin // We are in the audio data region
            // Don't account for forced transitions
            if (!force_toggle)
                if (subframe_which == LEFT && next_L == 1'b1)
                    parity_cnt <= parity_cnt + 1;
                else if (subframe_which == RIGHT && next_R == 1'b1)
                    parity_cnt <= parity_cnt + 1;
        end
        else if (bit_cnt == 61) begin // This is the channel status bit
            if (ch_bit)
                parity_cnt <= parity_cnt + 1;
        end
    end
end

assign parity = parity_cnt[0];

//////////////////////////////////
////    CHANNEL STATUS BIT    ////
//////////////////////////////////
// THIS IS NOT IMPLEMENTED!!
assign ch_bit = 0;



`ifdef SVA_ON

default clocking def_clk @(posedge clk); endclocking

property VALID_WIDTH;
    (SAMPLE_WIDTH inside {16, 20, 24});
endproperty

AST_VALID_WIDTH: assert property (VALID_WIDTH);

`endif

endmodule
