package spdif_aes3_transmitter_pkg;

typedef enum logic {LEFT, RIGHT} subframe_t;

typedef enum logic [7:0] {
    RESET = '0,                  // Reset value is all bits zero
    PREAMBLE_Z_0 = 8'b0001_0111, // Preamble Z when previous state was 0
    PREAMBLE_Z_1 = 8'b1110_1000, // Preamble Z when previous state was 1
    PREAMBLE_Y_0 = 8'b0010_0111, // Preamble Y when previous state was 0
    PREAMBLE_Y_1 = 8'b1110_0100, // Preamble Y when previous state was 1
    PREAMBLE_X_0 = 8'b0100_0111, // Preamble X when previous state was 0
    PREAMBLE_X_1 = 8'b1110_0010  // Preamble X when previous state was 1
} preamble_t;

endpackage