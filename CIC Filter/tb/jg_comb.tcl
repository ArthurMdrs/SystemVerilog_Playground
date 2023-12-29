clear -all

analyze -sv12 +define+SVA_ENABLE=1 ../rtl/comb.sv 
analyze -sv12 +define+SVA_ENABLE=1 ./comb_vc.sv 
#elaborate -top comb -create_related_covers witness
elaborate -top comb -create_related_covers witness -parameter {WIDTH} {8} -parameter {N_DELAYS} {4}

clock clk

#reset !rstn
reset -none
assume -reset !rstn

prove -all
