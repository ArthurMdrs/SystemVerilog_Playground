/*
    This is a verification component with SVA code for the decimator module.
    decimator.sv is in ../rtl/
*/

module decimator_vc #(
    int WIDTH = 1,
    int DEC_RATE = 4
) (
    input logic [WIDTH-1:0] out,
    input logic [WIDTH-1:0] in,
    input logic             clk,
    input logic             rstn,
    input logic             clk_slow
);

`ifdef SVA_SMLBLK

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
property VALID_OUTPUT (clk_slow, out, in, dec_rate);
    ($rose(clk_slow)) |=> ($stable(out))[*dec_rate-1];
endproperty

property RECOVER_AFTER_RESET (out, in, dec_rate);
    $rose(rstn) |-> ##[1:dec_rate] ($stable(out))[*dec_rate-1];
endproperty

property SIGNAL_RESETS (signal, rst_val);
    disable iff (1'b0)
    (!rstn) |-> (signal == rst_val);
endproperty

// Assertions
AST_VALID_OUTPUT: assert property (VALID_OUTPUT(clk_slow, out, in, DEC_RATE));
AST_RECOVER_AFTER_RESET: assert property (RECOVER_AFTER_RESET(out, in, DEC_RATE));
AST_OUT_RESETS: assert property (SIGNAL_RESETS(out, 0));

// Covers
property SIGNAL_CAN_BE_VALUE (signal, value);
    (signal != value)[*5] ##1 (signal == value);
endproperty

property NORMAL_RESET_BEHAVIOUR (signal);
    disable iff (1'b0)
    (rstn)[*5] ##1 (signal != 0) ##1 (!rstn) ##[*] (signal != 0);
endproperty

COV_OUTPUT_CAN_BE_3: cover property (SIGNAL_CAN_BE_VALUE(out, 3));
COV_NORMAL_RESET_BEHAVIOUR: cover property (NORMAL_RESET_BEHAVIOUR(out));

`endif
    
endmodule