/*
    This is a decim_or_interp module intended to be used in a CIC filter.

    RATE is either the decimation rate or interpolation rate.
    DnI (decimation-not-interpolation) is a flag that determines if the
    operation mode is decimation (flag high) or interpolation (flag low).

    Fast clock and slow clock relation:
    slow freq = fast freq / RATE

    Decimation: while input is driven at clk_fast speed, the output is 
    sampled from the input at clk_slow speed. This means that every RATE
    input samples, RATE-1 are dropped.

    Interpolation: while input is driven at clk_slow speed, the output is 
    sampled from the input at clk_fast speed every RATE clk_fast cycles.
    The rest of the cycles are filled with 0s. This means that every RATE
    output samples, 1 is equal to the input and RATE-1 are 0.
*/

module decim_or_interp #(
    int WIDTH = 1,
    int RATE = 4, // must be power of 2
    bit DnI = 1 // decimator = 1, interpolator = 0
) (
    output logic [WIDTH-1:0] out,
    input  logic [WIDTH-1:0] in,
    input  logic             clk_slow,
    input  logic             clk_fast,
    input  logic             rstn
);

// Drive output
generate
    // Decimator mode
    if (DnI) begin
        always_ff @(posedge clk_slow or negedge rstn) begin
            if (!rstn) 
                out <= 0;
            else
                out <= in;
        end


    // Interpolator mode
    end else begin
        logic [$clog2(RATE)-1:0] cnt;
        always_ff @(posedge clk_fast or negedge rstn) begin
            if (!rstn) begin
                out <= 0;
                cnt <= 0;
            end else begin
                cnt <= cnt + 1;
                if (cnt == 0)
                    out <= in;
                else
                    out <= 0;
            end
        end
    end
endgenerate



`ifdef SVA_SMLBLK

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

`endif
    
endmodule