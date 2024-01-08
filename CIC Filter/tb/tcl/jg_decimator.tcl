clear -all

analyze -sv12 +define+SVA_SMLBLK=1 ../rtl/decimator.sv 
analyze -sv12 +define+SVA_SMLBLK=1 ./decimator_vc.sv 
#elaborate -top decimator -create_related_covers witness
elaborate -top decimator -create_related_covers witness -parameter {WIDTH} {8} -parameter {DEC_RATE} {4}
#elaborate -top decimator -create_related_covers witness -parameter {WIDTH} {32} -parameter {DEC_RATE} {8}

clock clk_fast
clock clk_slow -factor 4

reset !rstn
#reset -none
#assume -reset !rstn

prove -all
