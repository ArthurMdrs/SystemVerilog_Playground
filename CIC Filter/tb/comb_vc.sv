/*
    This is a verification component with SVA code for the comb module.
    comb.sv is in ../rtl/
*/

module comb_vc #(
    int WIDTH = 1,
    int N_DELAYS = 1
) (
    input logic [WIDTH-1:0] y,
    input logic             overflow,
    input logic [WIDTH-1:0] a,
    input logic             clk,
    input logic             rstn,
    input logic [WIDTH-1:0] delayed [N_DELAYS]
);

`ifdef SVA_SMLBLK

// Defaults
default clocking def_clk @(posedge clk); 
endclocking

default disable iff (!rstn);

// Aux code
logic[$clog2(N_DELAYS+1):0] delays_waited;
always_ff @(posedge clk or negedge rstn) begin
    if(!rstn)
        delays_waited <= 0;
    else if (delays_waited <= N_DELAYS)
        delays_waited <= delays_waited + 1;
end

// Properties
property PROPER_DELAY (delayed, in, n_delays);
    (delays_waited >= n_delays) |-> (delayed == $past(in, n_delays));
endproperty

property VALID_OUTPUT (out, in, n_delays, overflow);
    (delays_waited  > n_delays) |-> (out == $past(in) - $past(in, n_delays+1)) || (overflow);
endproperty

property SIGNAL_RESETS (signal, rst_val);
    disable iff (1'b0)
    (!rstn) |-> (signal == rst_val);
endproperty

// Assertions
AST_PROPER_DELAY: assert property (PROPER_DELAY(delayed [N_DELAYS-1], a, N_DELAYS));
AST_VALID_OUTPUT: assert property (VALID_OUTPUT(y, a, N_DELAYS, overflow));
AST_Y_RESETS: assert property (SIGNAL_RESETS(y, 0));
AST_OVERFLOW_RESETS: assert property (SIGNAL_RESETS(overflow, 0));

// Covers
COV_OUTPUT_CAN_BE_3: cover property (
    (y != 3)[*(N_DELAYS+5)] ##1 (y == 3)
);
// COV_OVERFLOW_THEN_NOT_OVERFLOW: cover property (
//     (!overflow)[*(N_DELAYS+5)] ##[+] (y == 2**WIDTH-1) ##[+] (overflow) ##[+] (!overflow)
// );
COV_NORMAL_RESET_BEHAVIOUR: cover property (
    disable iff (1'b0)
    (rstn)[*5] ##1 (y != 0) ##1 (!rstn) ##[*] (y != 0)
);

`endif
    
endmodule