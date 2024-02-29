module ima_adpcm_decoder #(
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        sop,      // Start of packet
    input  logic        eop,      // End of packet
    input  logic [ 3:0] coded_i,  // Compressed (encoded) input data
    output logic [15:0] decoded_o // Decompressed (decoded) output data
);
    
    // Decoding Tables
    logic signed [7:0] ima_index_table [16] = '{
        -1, -1, -1, -1, 2, 4, 6, 8,
        -1, -1, -1, -1, 2, 4, 6, 8
    };
    logic signed [15:0] ima_step_table [89] = '{ 
            7,     8,     9,    10,    11,    12,    13,    14,    16,    17, 
           19,    21,    23,    25,    28,    31,    34,    37,    41,    45, 
           50,    55,    60,    66,    73,    80,    88,    97,   107,   118, 
          130,   143,   157,   173,   190,   209,   230,   253,   279,   307,
          337,   371,   408,   449,   494,   544,   598,   658,   724,   796,
          876,   963,  1060,  1166,  1282,  1411,  1552,  1707,  1878,  2066, 
         2272,  2499,  2749,  3024,  3327,  3660,  4026,  4428,  4871,  5358,
         5894,  6484,  7132,  7845,  8630,  9493, 10442, 11487, 12635, 13899, 
        15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767 
    };

    // Other variables
    logic signed [16:0] predictor , predictor_n ;
    logic signed [ 7:0] step_index, step_index_n;
    logic signed [15:0] step      , step_n      ;
    logic signed [16:0] diff;

    logic [ 3:0] coded_i_buf;
    
    logic decoding, decoding_l;

    // Buffer the input data
    always_ff @(posedge clk) begin
        if(!rst_n) begin
            coded_i_buf <= '0;
        end
        else if (sop || decoding) begin
            coded_i_buf <= coded_i;
        end
    end

    // Update decoding status
    always_ff @(posedge clk) begin
        if(!rst_n) begin
            decoding   <= 1'b0;
            decoding_l <= 1'b0;
        end
        else begin
            if (sop)
                decoding <= 1'b1;
            else if (eop)
                decoding <= 1'b0;
            decoding_l <= decoding;
        end
    end

    // Update registers of decoding process
    always_ff @(posedge clk) begin
        if(!rst_n) begin
            predictor  <= '0;
            step_index <= '0;
            step       <= ima_step_table[0];
        end
        else if (decoding || decoding_l) begin
            predictor  <= predictor_n;
            step_index <= step_index_n;
            step       <= step_n;
        end
    end
    
    // Calculate next value of registers
    always_comb begin
        step_index_n = step_index + ima_index_table[coded_i_buf];
             if (step_index_n <  0) step_index_n = 0;
        else if (step_index_n > 88) step_index_n = 88;
        
        step_n       = ima_step_table[step_index_n];
        
        predictor_n  = predictor + diff;
             if (predictor_n < -32768) predictor_n = -32768;
        else if (predictor_n >  32767) predictor_n =  32767;
    end   
    
    
    
    // Calculate diff
    // diff = ((signed)nibble + 0.5) * step / 4
    always_comb begin
        // diff = step >> 3;
        // if (coded_i_buf[2])
        //     diff += (step     );
        // if (coded_i_buf[1])
        //     diff += (step >> 1);
        // if (coded_i_buf[0])
        //     diff += (step >> 2);
        // if (coded_i_buf[3])
        //     diff = -diff;
            
        logic [19:0] diff_big;
        diff_big = step;
        if (coded_i_buf[2])
            diff_big += (step << 3);
        if (coded_i_buf[1])
            diff_big += (step << 2);
        if (coded_i_buf[0])
            diff_big += (step << 1);  
        // // Rounding: up if >= .5, down if < .5
        // // diff_big = diff_big + {16'b0, diff_big[2], 3'b0};      
        // Account for signal
        if (coded_i_buf[3])
            diff_big = -diff_big;       
        // Divide by 8
        diff = diff_big >> 3;
        
        // if (coded_i_buf[3])
        //     diff = -diff;
    end
    
    // Drive output 
    assign decoded_o = predictor[15:0];

endmodule

        // // Rounding: up if >= .5, down if < .5
        // // if (diff_big[2] == 1'b1)
        // //     diff_big = diff_big + 20'b01000; 
        // // diff_big = diff_big + {16'b0, diff_big[2], 3'b0};