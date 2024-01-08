/*
    This is a verification component with SVA code for the CIC filter module.
    CIC_filter.sv is in ../rtl/
*/

module CIC_filter_vc #(
    int WIDTH = 1,
    int STAGES = 1,
    int RATE = 4 // must be power of 2 and at least 2
) (
    input  logic [WIDTH-1:0] out,
    input  logic [WIDTH-1:0] in,
    input  logic             clk,
    input  logic             rstn,
    input  logic             clk_fast,
    input  logic             clk_slow
);

`ifdef SVA_BIGBLK

// Defaults
default clocking def_clk @(posedge clk); 
endclocking

default disable iff (!rstn);

// Aux code
logic delay;
always_ff @(posedge clk or negedge rstn) begin
    if(!rstn)
        delay <= 0;
    else
        delay <= 1;
end

// Properties
property SIGNAL_CAN_BE_VALUE (signal, value);
    (signal != value)[*5] ##1 (signal == value);
endproperty

property SIGNAL_IS_POWER_OF_2 (signal);
    ($onehot(signal));
endproperty

property SIGNAL_IS_AT_LEAST_2 (signal);
    (signal >= 2);
endproperty

property CLK_RELATION (clk_fast, clk_slow, rate);
    // @(posedge clk_fast)
    ($rose(clk_slow)) |=>  $stable(clk_slow)[*(rate/2-1)];
endproperty

// Assertions
AST_RATE_IS_POWER_OF_2: assert property (SIGNAL_IS_POWER_OF_2(RATE));
AST_RATE_IS_AT_LEAST_2: assert property (SIGNAL_IS_AT_LEAST_2(RATE));
AST_CLK_RELATION: assert property (CLK_RELATION(clk_fast, clk_slow, RATE));

// Covers
COV_OUTPUT_CAN_BE_3: cover property (SIGNAL_CAN_BE_VALUE(out, 3));

`endif
    
endmodule