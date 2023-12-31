/*
    This is a integrator module intended to be used in a CIC filter.
    The output follows the equation:
        a(n) = x(n) + a(n-1)
*/

module integrator #(
    int WIDTH = 1
) (
    output logic [WIDTH-1:0] a,
    output logic             overflow,
    input  logic [WIDTH-1:0] x,
    input  logic             clk,
    input  logic             rstn
);

// Drive outputs
always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        a <= 0;
        overflow <= 0;
    end else begin
        {overflow, a} <= x + a;
    end
end



`ifdef SVA_SMLBLK

bind integrator integrator_vc #(
    .WIDTH(WIDTH)
) integrator_vc_inst (
    .a,
    .overflow,
    .x,
    .clk,
    .rstn
);

`endif
    
endmodule