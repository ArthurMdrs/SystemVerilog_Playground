clear -all

analyze -sv12 \
    ../rtl/pkg/waveform_gen_pkg.sv \
    ../rtl/clk_gen.sv \
    ../rtl/sine_lut.sv \
    ../rtl/waveform_gen.sv

elaborate -top waveform_gen -create_related_covers witness -parameter {SEL_WIDTH} {8}

clock clk

reset !rst_n

prove -all
