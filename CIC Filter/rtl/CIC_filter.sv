/*
    CIC filters are moving average filters used for decimation and interpolation.

    The filter's size (or the filter's length) is how many samples it uses to
    calculate the average.

    As you can cascade many CIC filters in series, the STAGES parameter defines
    how many filter stages there are.

    The decimation/interpolation rate is equal to the filter's length.
    I.e. averaging the last 8 samples means the rate is 8. 

    DnI (decimation-not-interpolation) is a flag that determines if the
    operation mode is decimation (flag high) or interpolation (flag low).

    Data is assumed to be unsigned.
*/

module CIC_filter #(
    int WIDTH = 1,
    int STAGES = 1,
    int RATE = 4, // must be power of 2 and at least 2
    bit DnI = 1 // decimator = 1, interpolator = 0
) (
    output logic [WIDTH-1:0] out,
    input  logic [WIDTH-1:0] in,
    input  logic             clk,
    input  logic             rstn
);

// Clock generation
// Fast freq = sample freq, slow freq = fast freq / RATE
logic [$clog2(RATE/2):0] cnt;
logic clk_slow, clk_fast;

assign clk_fast = clk;

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

// Create adequate width for datapath registers
localparam int REGS_WIDTH = WIDTH + (STAGES * $clog2(RATE));

// Create inputs and outputs for combs and integrators
logic [REGS_WIDTH-1:0] integ_in  [STAGES];
logic [REGS_WIDTH-1:0] integ_out [STAGES];
logic [REGS_WIDTH-1:0] comb_in   [STAGES];
logic [REGS_WIDTH-1:0] comb_out  [STAGES];

// Vectors of overflow signals (these aren't used anywhere)
logic integ_of_vec [STAGES];
logic comb_of_vec  [STAGES];

// Generate filter stages
generate
    genvar i;
    for (i = 0; i < STAGES; i++) begin
        integrator #(
            .WIDTH(REGS_WIDTH)
        ) integrator_inst (
            .a(integ_out[i]),
            .overflow(integ_of_vec[i]),
            .x(integ_in[i]),
            .clk(clk_fast),
            .rstn(rstn)
        );

        comb #(
            .WIDTH(REGS_WIDTH),
            .N_DELAYS(1)
        ) comb_inst (
            .y(comb_out[i]),
            .overflow(comb_of_vec[i]),
            .a(comb_in[i]),
            .clk(clk_slow),
            .rstn(rstn)
        );

        if (i > 0) begin
            assign integ_in[i] = integ_out[i-1];
            assign  comb_in[i] =  comb_out[i-1];
        end
    end    
endgenerate

// decimator #(
//     .WIDTH(REGS_WIDTH),
//     .DEC_RATE(RATE)
// ) decimator_inst (
//     .out(comb_in[0]),
//     .in(integ_out[STAGES-1]),
//     .clk_slow(clk_slow),
//     .clk_fast(clk_fast),
//     .rstn(rstn)
// );

// Create input and output for decimator/interpolator block
logic [REGS_WIDTH-1:0] doi_in;
logic [REGS_WIDTH-1:0] doi_out;

// assign doi_out = (DnI) ? comb_in[0] : integ_in[0];
assign doi_in  = (DnI) ? integ_out[STAGES-1] : comb_out[STAGES-1];

decim_or_interp #(
    .WIDTH(REGS_WIDTH),
    .RATE(RATE),
    .DnI(DnI)
) decim_or_interp_inst (
    .out(doi_out),
    .in(doi_in),
    .clk_slow(clk_slow),
    .clk_fast(clk_fast),
    .rstn(rstn)
);

// The first stage input of each comb or integ depends on DnI mode
// It is either the module input or the decim/interp output
assign integ_in[0] = (DnI) ? {{(REGS_WIDTH-WIDTH){1'b0}}, in} : doi_out;
assign  comb_in[0] = (DnI) ? doi_out : {{(REGS_WIDTH-WIDTH){1'b0}}, in};

// Drive the output
// The output also depends on DnI mode
// It is the output of either the last comb or last integ
// The decimator's gain is also different than the interpolator's
always_comb begin
    if (DnI) // decimator
        out =  comb_out[STAGES-1] >> (STAGES * $clog2(RATE));
    else     // interpolator
        out = integ_out[STAGES-1] >> ((STAGES-1) * $clog2(RATE));
end

// assign out = comb_out[STAGES-1] >> (STAGES * $clog2(RATE));
// assign out = comb_out[STAGES-1] >> ($clog2(RATE**STAGES));



`ifdef SVA_BIGBLK

bind CIC_filter CIC_filter_vc #(
    .WIDTH(WIDTH),
    .STAGES(STAGES),
    .RATE(RATE)
) CIC_filter_vc_inst (
    .out,
    .in,
    .clk,
    .rstn,
    .clk_slow,
    .clk_fast
);

bind decim_or_interp decim_or_interp_vc #(
    .WIDTH(WIDTH), 
    .RATE(RATE), 
    .DnI(DnI)
) decim_or_interp_vc_inst (
    .out,
    .in,
    .clk_slow,
    .clk_fast,
    .rstn
);

bind integrator integrator_vc #(
    .WIDTH(WIDTH)
) integrator_vc_inst (
    .a,
    .overflow,
    .x,
    .clk,
    .rstn
);

bind comb comb_vc #(
    .WIDTH(WIDTH),
    .N_DELAYS(N_DELAYS)
) comb_vc_inst (
    .y,
    .overflow,
    .a,
    .clk,
    .rstn,
    .delayed
);

`endif
    
endmodule