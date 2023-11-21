/*
    Use the following python code to generate the contents
    of the always_comb block:

    n_bits = 52
    my_str = "if      (in[" + str(n_bits-1) + "]) out =  0;\n"
    for i in range(0, n_bits-1):
    if (n_bits-2-i < 10):
        my_str = my_str + "else if (in[ " + str(n_bits-2-i) + "]) out =  " + str(i+1) + ";\n"
    else:
        my_str = my_str + "else if (in[" + str(n_bits-2-i) + "]) out =  " + str(i+1) + ";\n"
    my_str = my_str + "else             out =  " + str(n_bits) + ";\n"
    print(my_str)

    Number of bits in input: n_bits used in the code above
    Number of bits in output: $clog2(n_bits)

*/

module count_leading_zeros (
    input  logic [51:0] in,
    output logic [5:0] out
);

    always_comb begin
        if      (in[51]) out =  0;
        else if (in[50]) out =  1;
        else if (in[49]) out =  2;
        else if (in[48]) out =  3;
        else if (in[47]) out =  4;
        else if (in[46]) out =  5;
        else if (in[45]) out =  6;
        else if (in[44]) out =  7;
        else if (in[43]) out =  8;
        else if (in[42]) out =  9;
        else if (in[41]) out =  10;
        else if (in[40]) out =  11;
        else if (in[39]) out =  12;
        else if (in[38]) out =  13;
        else if (in[37]) out =  14;
        else if (in[36]) out =  15;
        else if (in[35]) out =  16;
        else if (in[34]) out =  17;
        else if (in[33]) out =  18;
        else if (in[32]) out =  19;
        else if (in[31]) out =  20;
        else if (in[30]) out =  21;
        else if (in[29]) out =  22;
        else if (in[28]) out =  23;
        else if (in[27]) out =  24;
        else if (in[26]) out =  25;
        else if (in[25]) out =  26;
        else if (in[24]) out =  27;
        else if (in[23]) out =  28;
        else if (in[22]) out =  29;
        else if (in[21]) out =  30;
        else if (in[20]) out =  31;
        else if (in[19]) out =  32;
        else if (in[18]) out =  33;
        else if (in[17]) out =  34;
        else if (in[16]) out =  35;
        else if (in[15]) out =  36;
        else if (in[14]) out =  37;
        else if (in[13]) out =  38;
        else if (in[12]) out =  39;
        else if (in[11]) out =  40;
        else if (in[10]) out =  41;
        else if (in[ 9]) out =  42;
        else if (in[ 8]) out =  43;
        else if (in[ 7]) out =  44;
        else if (in[ 6]) out =  45;
        else if (in[ 5]) out =  46;
        else if (in[ 4]) out =  47;
        else if (in[ 3]) out =  48;
        else if (in[ 2]) out =  49;
        else if (in[ 1]) out =  50;
        else if (in[ 0]) out =  51;
        else             out =  52;
    end

endmodule