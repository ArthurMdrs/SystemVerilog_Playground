package waveform_gen_pkg;

    typedef enum logic [1:0] {
        SINE_WAVE,
        SAWTOOTH_WAVE,
        TRIANGULAR_WAVE,
        RECTANGULAR_WAVE
    } wave_sel_t;

    localparam int LUT_WIDTH = 16;                  // Number of bits in LUT output
    localparam int LUT_SIZE  = 32;                  // Number of entries in the LUT
    localparam int CNT_WIDTH = $clog2(LUT_SIZE);   // Number of bits in the counter

endpackage