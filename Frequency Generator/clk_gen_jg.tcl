clear -all

analyze -sv12 +define+SVA_ON ./clk_gen.sv

elaborate -top clk_gen -create_related_covers witness -parameter {SEL_WIDTH} {8}

clock clk_i

reset !rst_n

prove -all
