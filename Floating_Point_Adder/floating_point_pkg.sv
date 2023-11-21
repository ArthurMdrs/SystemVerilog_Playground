package floating_point_pkg;

    localparam int exp_width = 11;
    localparam int sig_width = 52;
    localparam int tot_width = 1 + exp_width + sig_width;
    localparam int exp_bias  = 2**(exp_width-1) - 1;

    typedef struct packed {
        logic                 sign;
        logic [exp_width-1:0] exponent;
        logic [sig_width-1:0] significand;
    } floating_point_number_t;

endpackage