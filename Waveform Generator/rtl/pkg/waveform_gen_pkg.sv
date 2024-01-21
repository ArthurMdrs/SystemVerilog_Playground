package waveform_gen_pkg;

    typedef enum logic [1:0] {
        SINE_WAVE,
        SAWTOOTH_WAVE,
        TRIANGULAR_WAVE,
        RECTANGULAR_WAVE
    } wave_sel_t;

    localparam int LUT_WIDTH = 16;

endpackage