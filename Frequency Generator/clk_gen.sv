/*
    This is a clock generator intended to generate various frequencies
    derived from an input clock, varying according to the frequency 
    selection input. 

    If (freq_sel == '1), output frequency equals input frequency,
    which is the maximum possible frequency.
    If (freq_sel == '0), output remains unchanged (freq = 0).
*/

`timescale 1ns/1ps

module clk_gen #(
    int SEL_WIDTH = 8
) (
    output logic                 clk_o,
    input  logic                 clk_i,
    input  logic [SEL_WIDTH-1:0] freq_sel,
    input  logic                 halt,
    input  logic                 rst_n
);

logic [SEL_WIDTH:0] accum;

always_ff @(posedge clk_i) begin
    if (!rst_n) begin
        accum <= '0;
    end else begin
        if (!halt)
            accum <= accum + freq_sel + 1;
    end
end

// Drive outputs
assign clk_o = accum[SEL_WIDTH];



`ifdef SVA_ON

default clocking def_clk @(posedge clk_i); endclocking

property STABLE_ON_HALT;
    (halt) |=> ($stable(clk_o));
endproperty

AST_STABLE_ON_HALT: assert property (STABLE_ON_HALT);

`endif
    
endmodule