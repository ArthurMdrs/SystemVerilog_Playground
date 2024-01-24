package waveform_gen_pkg;

    typedef enum logic [1:0] {
        SINE_WAVE,
        SAWTOOTH_WAVE,
        TRIANGULAR_WAVE,
        RECTANGULAR_WAVE
    } wave_sel_t;

    localparam int LUT_WIDTH = 16;
    localparam int CNT_WIDTH = $clog2(LUT_WIDTH);
    localparam int LUT_SIZE  = 16;

endpackage