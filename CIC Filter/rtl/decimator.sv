/*
    This is a decimator module intended to be used in a CIC filter.
    The output equals the input and holds its value for a certain
    amount of cycles before updating.
*/

module decimator #(
    int WIDTH = 1,
    int DEC_RATE = 4 // must be power of 2
) (
    output logic [WIDTH-1:0] out,
    input  logic [WIDTH-1:0] in,
    input  logic             clk,
    input  logic             rstn
);

// Counter counts for DEC_RATE cycles
// Generate slower clock based on the counter above
// logic [$clog2(DEC_RATE):0] cnt;
// logic clk_slow;

// always_ff @(posedge clk or negedge rstn) begin
//     if (!rstn) begin
//         cnt <= 0;
//         clk_slow <= 0;
//     end else if (cnt < DEC_RATE - 1) begin
//         cnt <= cnt + 1;
//         clk_slow <= 1;
//     end else begin
//         cnt <= 0;
//         clk_slow <= 0;
//     end
// end

logic [$clog2(DEC_RATE/2):0] cnt;
logic clk_slow;

always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        cnt <= 0;
        clk_slow <= 0;
    end else if (cnt < DEC_RATE/2 - 1) begin
        cnt <= cnt + 1;
    end else begin
        cnt <= 0;
        clk_slow <= !clk_slow;
    end
end

// Drive output
always_ff @(posedge clk_slow or negedge rstn) begin
    if (!rstn) 
        out <= 0;
    else
        out <= in;
end



`ifdef SVA_SMLBLK

bind decimator decimator_vc #(
    .WIDTH(WIDTH), 
    .DEC_RATE(DEC_RATE)
) decimator_vc_inst (
    .out,
    .in,
    .clk,
    .rstn,
    .clk_slow
);

`endif
    
endmodule