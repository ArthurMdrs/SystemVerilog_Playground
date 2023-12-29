clear -all

analyze -sv12 +define+SVA_ENABLE=1 ../rtl/decimator.sv 
analyze -sv12 +define+SVA_ENABLE=1 ./decimator_vc.sv 
#elaborate -top decimator -create_related_covers witness
elaborate -top decimator -create_related_covers witness -parameter {WIDTH} {8} -parameter {DEC_RATE} {4}
#elaborate -top decimator -create_related_covers witness -parameter {WIDTH} {32} -parameter {DEC_RATE} {8}

clock clk

reset !rstn
#reset -none
#assume -reset !rstn

prove -all
