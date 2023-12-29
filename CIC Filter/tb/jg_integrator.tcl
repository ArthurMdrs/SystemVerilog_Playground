clear -all

analyze -sv12 +define+SVA_ENABLE=1 ../rtl/integrator.sv 
analyze -sv12 +define+SVA_ENABLE=1 ./integrator_vc.sv 
#elaborate -top integrator -create_related_covers witness
elaborate -top integrator -create_related_covers witness -parameter {WIDTH} {16}

clock clk

#reset !rstn
reset -none
assume -reset !rstn

prove -all
