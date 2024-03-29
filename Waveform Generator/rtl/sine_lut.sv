/*
    This file was generated by `root_dir`/gen_lut.py
*/

module sine_lut #(
    localparam int OUT_WIDTH = 16,
    localparam int LUT_SIZE = 32,
    localparam int SEL_WIDTH = $clog2(LUT_SIZE)
) (
    output logic signed [OUT_WIDTH-1:0] sine_o,
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic        [SEL_WIDTH-1:0] lut_sel
);

always_ff @(posedge clk) begin
    if (!rst_n) begin
        sine_o <= 0;
    end else begin
        case(lut_sel)
            0: sine_o <= 16'sd0;
            1: sine_o <= 16'sd6393;
            2: sine_o <= 16'sd12539;
            3: sine_o <= 16'sd18204;
            4: sine_o <= 16'sd23170;
            5: sine_o <= 16'sd27245;
            6: sine_o <= 16'sd30273;
            7: sine_o <= 16'sd32137;
            8: sine_o <= 16'sd32767;
            9: sine_o <= 16'sd32137;
            10: sine_o <= 16'sd30273;
            11: sine_o <= 16'sd27245;
            12: sine_o <= 16'sd23170;
            13: sine_o <= 16'sd18204;
            14: sine_o <= 16'sd12539;
            15: sine_o <= 16'sd6393;
            16: sine_o <= 16'sd0;
            17: sine_o <= -16'sd6393;
            18: sine_o <= -16'sd12539;
            19: sine_o <= -16'sd18204;
            20: sine_o <= -16'sd23170;
            21: sine_o <= -16'sd27245;
            22: sine_o <= -16'sd30273;
            23: sine_o <= -16'sd32137;
            24: sine_o <= -16'sd32767;
            25: sine_o <= -16'sd32137;
            26: sine_o <= -16'sd30273;
            27: sine_o <= -16'sd27245;
            28: sine_o <= -16'sd23170;
            29: sine_o <= -16'sd18204;
            30: sine_o <= -16'sd12539;
            31: sine_o <= -16'sd6393;
        endcase
    end
end

endmodule
