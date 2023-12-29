/*
    This is a verification component with SVA code for the integrator module.
    integrator.sv is in ../rtl/
*/

module integrator_vc #(
    int WIDTH = 1
) (
    input logic [WIDTH-1:0] a,
    input logic             overflow,
    input logic [WIDTH-1:0] x,
    input logic             clk,
    input logic             rstn,
    input logic [WIDTH-1:0] delayed
);

`ifdef SVA_ENABLE

// Defaults
default clocking def_clk @(posedge clk); 
endclocking

default disable iff (!rstn);

// Aux code
localparam int N_DELAYS = 1;
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

property VALID_OUTPUT (out, in1, in2, n_delays, overflow);
    (delays_waited  > n_delays) |-> (out == $past(in1) + $past(in2, n_delays+1)) || (overflow);
endproperty

property SIGNAL_RESETS (signal, rst_val);
    disable iff (1'b0)
    (!rstn) |-> (signal == rst_val);
endproperty

// Assertions
AST_PROPER_DELAY: assert property (PROPER_DELAY(delayed, a, N_DELAYS));
AST_VALID_OUTPUT: assert property (VALID_OUTPUT(a, x, a, N_DELAYS, overflow));
AST_A_RESETS: assert property (SIGNAL_RESETS(a, 0));
AST_OVERFLOW_RESETS: assert property (SIGNAL_RESETS(overflow, 0));

// Covers
COV_OUTPUT_CAN_BE_3: cover property (
    (a != 3)[*(N_DELAYS+5)] ##1 (a == 3)
);
COV_OVERFLOW_THEN_NOT_OVERFLOW: cover property (
    (!overflow)[*(N_DELAYS+5)] ##[+] (a == 2**WIDTH-1) ##[+] (overflow) ##[+] (!overflow)
);
COV_NORMAL_RESET_BEHAVIOUR: cover property (
    disable iff (1'b0)
    (rstn)[*5] ##1 (a != 0) ##1 (!rstn) ##[*] (a != 0)
);

`endif
    
endmodule