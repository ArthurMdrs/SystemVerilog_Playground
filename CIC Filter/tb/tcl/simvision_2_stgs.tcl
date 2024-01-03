
# XM-Sim Command File
# TOOL:	xmsim(64)	23.09-s003
#
#
# You can restore this configuration with:
#
#      xrun -64bit -sv ./CIC_filter_tb.sv ./CIC_filter_vc.sv ./comb_vc.sv ./decimator_vc.sv ./integrator_vc.sv ../rtl/CIC_filter.sv ../rtl/comb.sv ../rtl/decimator.sv ../rtl/integrator.sv +define+SVA_BIGBLK=1 -top CIC_filter_tb -timescale 1ns/1ns -access +rwc +SVSEED=random -s -input /home/pedro.medeiros/SystemVerilog_Playground/CIC Filter/tb/tcl/simvision_2_stgs.tcl
#

set tcl_prompt1 {puts -nonewline "xcelium> "}
set tcl_prompt2 {puts -nonewline "> "}
set vlog_format %h
set vhdl_format %v
set real_precision 6
set display_unit auto
set time_unit module
set heap_garbage_size -200
set heap_garbage_time 0
set assert_report_level note
set assert_stop_level error
set autoscope yes
set assert_1164_warnings yes
set pack_assert_off {}
set severity_pack_assert_off {note warning}
set assert_output_stop_level failed
set tcl_debug_level 0
set relax_path_name 1
set vhdl_vcdmap XX01ZX01X
set intovf_severity_level ERROR
set probe_screen_format 0
set rangecnst_severity_level ERROR
set textio_severity_level ERROR
set vital_timing_checks_on 1
set vlog_code_show_force 0
set assert_count_attempts 1
set tcl_all64 false
set tcl_runerror_exit false
set assert_report_incompletes 0
set show_force 1
set force_reset_by_reinvoke 0
set tcl_relaxed_literal 0
set probe_exclude_patterns {}
set probe_packed_limit 4k
set probe_unpacked_limit 16k
set assert_internal_msg no
set svseed -1588351762
set assert_reporting_mode 0
set vcd_compact_mode 0
set vhdl_forgen_loopindex_enum_pos 0
alias . run
alias indago verisium
alias quit exit
database -open -shm -into waves.shm waves -default
probe -create -database waves CIC_filter_tb.clk CIC_filter_tb.in CIC_filter_tb.CIC_filter_inst.genblk1[0].integrator_inst.x[9:0] CIC_filter_tb.CIC_filter_inst.genblk1[0].integrator_inst.a[9:0] CIC_filter_tb.CIC_filter_inst.genblk1[1].integrator_inst.x CIC_filter_tb.CIC_filter_inst.genblk1[1].integrator_inst.a CIC_filter_tb.CIC_filter_inst.decimator_inst.in[9:0] CIC_filter_tb.CIC_filter_inst.decimator_inst.out[9:0] CIC_filter_tb.CIC_filter_inst.genblk1[0].comb_inst.a[9:0] CIC_filter_tb.CIC_filter_inst.genblk1[0].comb_inst.y[9:0] CIC_filter_tb.CIC_filter_inst.genblk1[1].comb_inst.a CIC_filter_tb.CIC_filter_inst.genblk1[1].comb_inst.y CIC_filter_tb.out CIC_filter_tb.last_samples CIC_filter_tb.accum CIC_filter_tb.last_sum CIC_filter_tb.last_avg CIC_filter_tb.my_cnt

simvision -input simvision_2_stgs.tcl.svcf
