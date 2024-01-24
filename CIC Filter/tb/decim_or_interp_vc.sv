/*
    This is a verification component with SVA code for the decim_or_interp module.
    decim_or_interp.sv is in ../rtl/
*/

module decim_or_interp_vc #(
    int WIDTH = 1,
    int RATE = 4, // must be power of 2
    bit DnI = 1 // decimator = 1, interpolator = 0
) (
    input logic [WIDTH-1:0] out,
    input logic [WIDTH-1:0] in,
    input logic             clk_slow,
    input logic             clk_fast,
    input logic             rstn
);

`ifdef SVA_SMLBLK

// Defaults
default clocking def_clk @(posedge clk_fast); 
endclocking

default disable iff (!rstn);

// Aux code
logic delay;
always_ff @(posedge clk_fast or negedge rstn) begin
    if(!rstn)
        delay <= 0;
    else
        delay <= 1;
end

// Properties
property VALID_DECIMATOR (clk_slow, dni, out, rate);
    ($rose(clk_slow) && dni) |=> ($stable(out))[*rate-1];
endproperty

property VALID_INTERPOLATOR (dni, out, rate);
    ((!dni) && (out != 0)) |=> (out == 0)[*rate-1];
endproperty

property SIGNAL_IS_POWER_OF_2 (signal);
    ($onehot(signal));
endproperty

property SIGNAL_IS_AT_LEAST_2 (signal);
    (signal >= 2);
endproperty

// Assertions
AST_VALID_DECIMATOR: assert property (VALID_DECIMATOR(clk_slow, DnI, out, RATE));
AST_VALID_INTERPOLATOR: assert property (VALID_INTERPOLATOR(DnI, out, RATE));
AST_RATE_IS_POWER_OF_2: assert property (SIGNAL_IS_POWER_OF_2(RATE));
AST_RATE_IS_AT_LEAST_2: assert property (SIGNAL_IS_AT_LEAST_2(RATE));

// Covers
property SIGNAL_CAN_BE_VALUE (signal, value);
    (signal != value)[*5] ##1 (signal == value);
endproperty

COV_OUTPUT_CAN_BE_3: cover property (SIGNAL_CAN_BE_VALUE(out, 3));

// Reset checks below
// There should be "reset -none" and "assume -reset !rstn" in the Jasper tcl file
property RECOVER_AFTER_RESET (out, in, rate);
    $rose(rstn) |-> ##[1:rate] ($stable(out))[*rate-1];
endproperty

property SIGNAL_RESETS (signal, rst_val);
    disable iff (1'b0)
    (!rstn) |-> (signal == rst_val);
endproperty

property NORMAL_RESET_BEHAVIOUR (signal);
    disable iff (1'b0)
    (rstn)[*5] ##1 (signal != 0) ##1 (!rstn) ##[*] (signal != 0);
endproperty

AST_RECOVER_AFTER_RESET: assert property (RECOVER_AFTER_RESET(out, in, RATE));
AST_OUT_RESETS: assert property (SIGNAL_RESETS(out, 0));

COV_NORMAL_RESET_BEHAVIOUR: cover property (NORMAL_RESET_BEHAVIOUR(out));

`endif
    
endmodule