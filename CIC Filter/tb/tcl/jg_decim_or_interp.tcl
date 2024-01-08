clear -all

analyze -sv12 +define+SVA_SMLBLK=1 ../rtl/decim_or_interp.sv 
analyze -sv12 +define+SVA_SMLBLK=1 ./decim_or_interp_vc.sv 
#elaborate -top decim_or_interp -create_related_covers witness
elaborate -top decim_or_interp -create_related_covers witness -parameter {WIDTH} {8} -parameter {RATE} {4} -parameter {DnI} {0}
#elaborate -top decim_or_interp -create_related_covers witness -parameter {WIDTH} {32} -parameter {RATE} {8} -parameter {DnI} {0}

clock clk_fast
clock clk_slow -factor 4

reset !rstn
#reset -none
#assume -reset !rstn

prove -all
