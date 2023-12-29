/*
    This is a comb module intended to be used in a CIC filter.
    The output follows the equation:
        y(n) = a(n) - a(n-4)
*/

module comb #(
    int WIDTH = 1,
    int N_DELAYS = 1
) (
    output logic [WIDTH-1:0] y,
    output logic             overflow,
    input  logic [WIDTH-1:0] a,
    input  logic             clk,
    input  logic             rstn
);

// Declaration of delayed stages
logic [WIDTH-1:0] delayed [N_DELAYS];

// Drive delayed stages
always_ff @(posedge clk or negedge rstn) begin
    if (!rstn)
        delayed <= '{N_DELAYS{0}};
    else begin
        delayed[0] <= a;
        for (int i = 0; i < N_DELAYS-1; i++)  begin
            delayed[i+1] <= delayed[i];
        end
    end
end

// Drive outputs
always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        y <= 0;
        overflow <= 0;
    end else begin
        y <= a - delayed[N_DELAYS-1];
        overflow <= (a < delayed[N_DELAYS-1]);
    end
end



`ifdef SVA_ENABLE

bind comb comb_vc #(
    .WIDTH(WIDTH),
    .N_DELAYS(N_DELAYS)
) comb_vc_inst (
// ) (
    .y,
    .overflow,
    .a,
    .clk,
    .rstn,
    .delayed
);

`endif
    
endmodule