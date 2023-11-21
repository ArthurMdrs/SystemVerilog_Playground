module floating_point_adder_tb;

    // Import the package with typedefs
    import floating_point_pkg::*;

    // DUT signals
    floating_point_number_t op1, op2, res;
    logic invalid_res;

    // The DUT
    floating_point_adder DUT (.op1, .op2, .res, .invalid_res);

    // Simulation signals
    real op1_sim, op2_sim, res_sim;
    bit verbose = 1;
    int error_count = 0, exception_count = 0;

    // Enum for test selection
    typedef enum int {
        RANDOM_TEST, SAME_SIGN, HIGH_NUMBERS, LOW_NUMBERS, CLOSE_EXPONENTS
        } test_sel_t;
    test_sel_t test_sel = CLOSE_EXPONENTS;

    ////////////////////////  FUNCTIONS AND TASKS  ////////////////////////

    // Function to simulate reference model
    function void checkit (real expected, real actual, bit verbose = 1);
        real margin;
        bit inside_margin;
        margin = expected * $pow(2, -sig_width+4);
        // $display("Margin is %.20e.", margin);
        if (margin < 0) margin = -margin;
        inside_margin = (expected - actual < margin && expected - actual > -margin) ? 1 : 0;
        if (!inside_margin) begin
            $display("Mismatch.\nExpected %.20e\n     Got %.20e.", expected, actual);
            $display("Margin is %.20e.", margin);
            error_count++;
        end else if (verbose) begin
            $display("Match.");
        end
    endfunction : checkit

    function real fp2real (floating_point_number_t fp);
        fp2real = (-1.0)**fp.sign * {1'b1, fp.significand} * $pow(2, int'(fp.exponent - exp_bias - sig_width));
    endfunction

    task run_test (test_sel_t test_sel = RANDOM_TEST);        
        repeat (5000) begin
            $display("#=============================================#");
            case (test_sel)
                RANDOM_TEST: begin
                    void'(randomize(op1, op2) with {
                        // op1.exponent != '1;
                        // op2.exponent != '1;
                    });
                end
                SAME_SIGN: begin
                    void'(randomize(op1, op2) with {op1.sign == op2.sign;});
                end
                HIGH_NUMBERS: begin
                    void'(randomize(op1, op2) with {
                        op1.exponent >= {exp_width{1'b1}} - 10;
                        op2.exponent >= {exp_width{1'b1}} - 10;
                    });
                end
                LOW_NUMBERS: begin
                    void'(randomize(op1, op2) with {
                        op1.exponent <= 10;
                        op2.exponent <= 10;
                    });
                end
                CLOSE_EXPONENTS: begin
                    void'(randomize(op1, op2) with {
                        op1.exponent - op2.exponent <= 10 || op2.exponent - op1.exponent <= 10;
                    });
                end
            endcase
            op1_sim = fp2real(op1);
            op2_sim = fp2real(op2);

            #1;
            if (verbose) begin
                $display("Op1: %b_%0d_%b", op1.sign, op1.exponent, op1.significand);
                $display("Op2: %b_%0d_%b", op2.sign, op2.exponent, op2.significand);
                $display("Exponent diff: %0d", (op1.exponent >= op2.exponent) ? (op1.exponent - op2.exponent) : (op2.exponent - op1.exponent));
                $display("Chosen exponent: %0d", DUT.exponent);
                $display("Significand1   :  %b", DUT.significand1);
                $display("Significand2   :  %b", DUT.significand2);
                $display("Significand sum: %b", DUT.significand_sum);
                $display("Normalized sum :   %b", DUT.normalized_sum);
                $display("Is sum: %b", DUT.is_sum);
                $display("Leading zeroes: %0d", DUT.subtract_shift);
                $display("Normalized exponent: %0d", DUT.normalized_exp);
            end

            if (invalid_res)
                exception_count++;

            res_sim = fp2real(res);
            $display("%t Drove:", $realtime);
            $display("Op1 = %.4e, Op2 = %.4e", op1_sim, op2_sim);
            $display("Got Res = %.4e", res_sim);
            $display("Exception did%soccur.", invalid_res ? " " : " not ");
            checkit(.expected(op1_sim + op2_sim), .actual(res_sim), .verbose(verbose));
            $display("#=============================================#");
        end
    endtask

    ////////////////////////  INITIAL BLOCKS  ////////////////////////

    // The proccess
    initial begin
        // Specifying time format (%t)
        $timeformat(-9, 0, "ns", 7); // e.g.: " 1000ns"

        run_test (test_sel);

        $display("%0d mismatches occured.", error_count);
        $display("%0d exceptions occured.", exception_count);
        
        $finish;
    end

endmodule