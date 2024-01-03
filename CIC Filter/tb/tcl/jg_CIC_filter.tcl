clear -all

analyze -sv12 +define+SVA_BIGBLK=1 \
    ./CIC_filter_vc.sv \
    ../rtl/CIC_filter.sv \
    ../rtl/comb.sv \
    ../rtl/decimator.sv \
    ../rtl/integrator.sv
analyze -sv12 +define+SVA_SMLBLK=1 \
    ./comb_vc.sv \
    ./decimator_vc.sv \
    ./integrator_vc.sv
#elaborate -top CIC_filter -create_related_covers witness
elaborate -top CIC_filter -create_related_covers witness -parameter {WIDTH} {8} -parameter {STAGES} {3} -parameter {RATE} {4}

clock clk

reset !rstn
#reset -none
#assume -reset !rstn

prove -all
#prove -bg -property {<embedded>::CIC_filter.CIC_filter_vc_inst.COV_OUTPUT_CAN_BE_3}
