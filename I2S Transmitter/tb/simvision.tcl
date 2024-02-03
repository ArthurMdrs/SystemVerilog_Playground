
# XM-Sim Command File
# TOOL:	xmsim(64)	23.09-s003
#
#
# You can restore this configuration with:
#
#      xrun -timescale 1ns/1ps ../rtl/pkg/i2s_transmitter_pkg.sv ../rtl/i2s_transmitter.sv ./i2s_transmitter_tb.sv -access +rwc -s -input simvision.tcl
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
set svseed 1
set assert_reporting_mode 0
set vcd_compact_mode 0
set vhdl_forgen_loopindex_enum_pos 0
alias . run
alias indago verisium
alias quit exit
stop -create -name Randomize -randomize
database -open -shm -into waves.shm waves -default
probe -create -database waves i2s_transmitter_tb.clk i2s_transmitter_tb.rst_n i2s_transmitter_tb.ready i2s_transmitter_tb.tx_data i2s_transmitter_tb.SCLK i2s_transmitter_tb.SD i2s_transmitter_tb.WS
probe -create -database waves i2s_transmitter_tb.dut.tx_data_buffer
probe -create -database waves i2s_transmitter_tb.dut.state
probe -create -database waves i2s_transmitter_tb.dut.bit_cnt
probe -create -database waves i2s_transmitter_tb.dut.delayed_rst_n
probe -create -database waves i2s_transmitter_tb.rcv_data i2s_transmitter_tb.n_rcv_data

simvision -input simvision.tcl.svcf

run