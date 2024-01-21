/*
    This is a waveform generator intended to generate various 
*/

`timescale 1ns/1ps

module waveform_gen import waveform_gen_pkg::*; #(
    int SEL_WIDTH = 8
) (
    output logic signed [LUT_WIDTH-1:0] wave_o,
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic        [SEL_WIDTH-1:0] freq_sel,
    input  wave_sel_t                   wave_sel, 
    input  logic                        halt
);

// Frequency generator
logic clk_o;
clk_gen #(
    .SEL_WIDTH(SEL_WIDTH)
) clk_gen_inst (
    .clk_o,
    .clk_i(clk),
    .freq_sel,
    .halt,
    .rst_n
);

// Counter will be used as input to the LUTs
localparam int CNT_WIDTH = $clog2(LUT_WIDTH);
logic [CNT_WIDTH-1:0] my_cnt;
// always_ff @(posedge clk_o or negedge rst_n) begin
always @(clk_o or !rst_n) begin // Make it level-sensitive to not lose frequency
    if (!rst_n) begin
        my_cnt <= 0;
    end else begin
        my_cnt <= my_cnt + 1;
    end
end

// LUTs instantiations

logic signed [LUT_WIDTH-1:0] sine_o;
logic signed [LUT_WIDTH-1:0] sawtooth_o;
logic signed [LUT_WIDTH-1:0] triangular_o;

sine_lut sine_lut_inst (
    .sine_o,
    .clk,
    .rst_n,
    .lut_sel(my_cnt)
);

sawtooth_lut sawtooth_lut_inst (
    .sawtooth_o,
    .clk,
    .rst_n,
    .lut_sel(my_cnt)
);
// TO DO: add reverse sawtooth option!!

triangular_lut triangular_lut_inst (
    .triangular_o,
    .clk,
    .rst_n,
    .lut_sel(my_cnt)
);

// TO DO: add rectangular wave LUT!!

// Drive output
always_comb begin
    case(wave_sel)
        SINE_WAVE: wave_o = sine_o;
        SAWTOOTH_WAVE: wave_o = sawtooth_o;
        TRIANGULAR_WAVE: wave_o = triangular_o;
        RECTANGULAR_WAVE: wave_o = {LUT_WIDTH{my_cnt[CNT_WIDTH-1]}};
        default: wave_o = '0;
    endcase
end


`ifdef SVA_ON

`endif
    
endmodule