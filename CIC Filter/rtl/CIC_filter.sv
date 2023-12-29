/*
    CIC filters are moving average filters used for decimation and interpolation.
    This module implements the decimation function.

    The decimation/interpolation rate is equal to the filter's length.
    I.e. averaging the last 8 samples means the rate is 8. 
*/

module CIC_filter #(
    int WIDTH = 1,
    int STAGES = 1,
    int RATE = 4 // must be power of 2
) (
    output logic [WIDTH-1:0] out,
    input  logic [WIDTH-1:0] in,
    input  logic             clk,
    input  logic             rstn
);

localparam int REGS_WIDTH = WIDTH + (STAGES * $clog2(RATE));


logic [REGS_WIDTH-1:0] integ_in  [STAGES];
logic [REGS_WIDTH-1:0] integ_out [STAGES];
logic [REGS_WIDTH-1:0] comb_in   [STAGES];
logic [REGS_WIDTH-1:0] comb_out  [STAGES];
logic [REGS_WIDTH-1:0] decim_out;

// Clock generation
logic [$clog2(RATE/2):0] cnt;
logic clk_slow;

always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        cnt <= 0;
        clk_slow <= 0;
    end else if (cnt < RATE/2 - 1) begin
        cnt <= cnt + 1;
    end else begin
        cnt <= 0;
        clk_slow <= !clk_slow;
    end
end


generate
    genvar i;
    for (i = 0; i < STAGES; i++) begin
        integrator #(
            .WIDTH(REGS_WIDTH)
        ) integrator_inst (
            .a(integ_out[i]),
            .overflow(),
            .x(integ_in[i]),
            .clk(clk),
            .rstn(rstn)
        );

        comb #(
            .WIDTH(REGS_WIDTH),
            .N_DELAYS(1)
        ) comb_inst (
            .y(comb_out[i]),
            .overflow(),
            .a(comb_in[i]),
            .clk(clk_slow),
            .rstn(rstn)
        );

        if (i > 0) begin
            assign integ_in[i] = integ_out[i-1];
            assign comb_in[i]  = comb_out[i-1] ;
        end
    end    
endgenerate

decimator #(
    .WIDTH(REGS_WIDTH),
    .DEC_RATE(RATE)
) decimator_inst (
    .out(comb_in[0]),
    .in(integ_out[STAGES-1]),
    .clk(clk),
    .rstn(rstn)
);


assign integ_in[0] = {{(REGS_WIDTH-WIDTH){1'b0}}, in};


assign out = comb_out[STAGES-1] >> $clog2(RATE);
// assign out = comb_out[STAGES-1];



`ifdef SVA_ENABLE

bind CIC_filter CIC_filter_vc #(
    .WIDTH(WIDTH),
    .STAGES(STAGES),
    .RATE(RATE)
) CIC_filter_vc_inst
(
    .out,
    .in,
    .clk,
    .rstn
);

`endif
    
endmodule