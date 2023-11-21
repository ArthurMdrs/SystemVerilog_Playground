/*
    This is a combinational block for computation the addition of two double-precision 
    floating point numbers. 

    Inputs:  2 floating point operands.
    Outputs: 1 floating point result;
             1 flag for indicating overflow or underflow on the exponent.

    Rounding methods are not implemented. 
    Denormalized numbers are not handled.

    Algorithm:
    1. Compare exponents and shift the smaller number until the operands match.
    2. Add the significands. 
    3. Normalize the sum by either shifting right and incrementing the exponent or shifting
    left and decrementing the exponent. 
*/

module floating_point_adder import floating_point_pkg::*; (
    input  floating_point_number_t op1, op2,
    output floating_point_number_t res,
    output logic                   invalid_res
);

    // Significands including the invisible 1
    // With the invisible 1, we have size(new_significand) = size(old_significand) + 1
    logic [sig_width  :0] significand1, significand2;
    // Exponent that will be used for the calculation
    logic [exp_width-1:0] exponent;

    // Doing the necessary shifting to enforce same exponent on both significands
    always_comb begin
        if (op1.exponent > op2.exponent) begin
                significand1 = {1'b1, op1.significand};
                significand2 = {1'b1, op2.significand} >> (op1.exponent - op2.exponent);
                exponent = op1.exponent;
        end else begin
                significand1 = {1'b1, op1.significand} >> (op2.exponent - op1.exponent);
                significand2 = {1'b1, op2.significand};
                exponent = op2.exponent;
        end
    end

    // Sum (or subtraction) of the significands with attention to the sign
    // We increment 1 bit to the size to hold the carry bit from the addition
    logic [sig_width+1:0] significand_sum;
    // Sign of the final result can already be determined
    logic result_sign;
    // Knowing if we have a sum of subtraction will be useful
    logic is_sum;

    // Doing the operation
    always_comb begin
        if (op1.sign == op2.sign) begin // If same signs, we sum
            significand_sum = significand1 + significand2;
            result_sign = op1.sign;
            is_sum = 1;
        end else if (significand1 > significand2) begin // If different signs, subtract big - small
            significand_sum = significand1 - significand2;
            result_sign = op1.sign;
            is_sum = 0;
        end else begin
            significand_sum = significand2 - significand1;
            result_sign = op2.sign;
            is_sum = 0;
        end
    end

    // If we did a subtraction, we might need to shift the result by the amount
    // of leading zeros
    logic [$clog2(sig_width)-1:0] subtract_shift;
    count_leading_zeros leading_zeros (.in(significand_sum[sig_width-1:0]), .out(subtract_shift));

    // We need to normalize the sum obtained on the previous always_comb
    // This will be the final result, so back to the original size
    logic [sig_width-1:0] normalized_sum;
    // Normalizing the significand requires normalizing the exponent
    logic [exp_width-1:0] normalized_exp;
    // Exception indicates overflow or underflow
    logic exception; 

    // Normalizing the result
    always_comb begin
        if (is_sum) begin
            if (significand_sum[sig_width+1]) begin // Check the carry bit and shift the result
                normalized_sum = significand_sum >> 1;
                normalized_exp = exponent + 1;
                exception = (exponent + 1  >=  (1 << exp_width)); // Exponent overflow
            end else begin // If there was no carry, we don't have to shift
                normalized_sum = significand_sum;
                normalized_exp = exponent;
                exception = 0;
            end
        end else begin
            if (significand_sum[sig_width]) begin // If the MSB is 1, it is already normalized
                normalized_sum = significand_sum;
                normalized_exp = exponent;
                exception = 0;
            end else begin // If the MSB is 0, we shift by the leading zeros
                normalized_sum = significand_sum << (subtract_shift + 1);
                normalized_exp = exponent - (subtract_shift + 1);
                exception = ((exponent - (subtract_shift + 1))  >  exponent); // Exponent underflow
            end
        end
    end

    // The result is ready, assign to the output
    always_comb begin
        res.sign = result_sign;
        res.exponent = normalized_exp;
        res.significand = normalized_sum;
        invalid_res = exception;
    end

endmodule