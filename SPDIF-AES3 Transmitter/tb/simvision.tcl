
# XM-Sim Command File
# TOOL:	xmsim(64)	23.09-s003
#
#
# You can restore this configuration with:
#
#      xrun -64bit -sv ../rtl/pkg/spdif_aes3_transmitter_pkg.sv ./spdif_aes3_transmitter_tb.sv ../rtl/Untitled-1.sv ../rtl/spdif_aes3_transmitter.sv -top spdif_aes3_transmitter_tb -timescale 1ns/1ns -access +rwc +SVSEED=1 -s -input /home/pedro.medeiros/SystemVerilog_Playground/SPDIF-AES3 Transmitter/tb/simvision.tcl
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
probe -create -database waves spdif_aes3_transmitter_tb.clk spdif_aes3_transmitter_tb.rst_n spdif_aes3_transmitter_tb.sample_i spdif_aes3_transmitter_tb.dut.bit_cnt spdif_aes3_transmitter_tb.dut.preamble spdif_aes3_transmitter_tb.dut.sample_buffer_L spdif_aes3_transmitter_tb.dut.sample_buffer_R spdif_aes3_transmitter_tb.dut.subframe_cnt spdif_aes3_transmitter_tb.dut.subframe_which spdif_aes3_transmitter_tb.dut.tx_o spdif_aes3_transmitter_tb.dut.parity_cnt
probe -create -database waves spdif_aes3_transmitter_tb.dut.ready
probe -create -database waves spdif_aes3_transmitter_tb.dut.force_toggle
probe -create -database waves spdif_aes3_transmitter_tb.dut.audio_data_L spdif_aes3_transmitter_tb.dut.audio_data_R
probe -create -database waves spdif_aes3_transmitter_tb.dut.unmblk1.temp_var spdif_aes3_transmitter_tb.dec_clk spdif_aes3_transmitter_tb.dec_data spdif_aes3_transmitter_tb.dec_sample
probe -create -database waves spdif_aes3_transmitter_tb.tx_o_valid
probe -create -database waves spdif_aes3_transmitter_tb.dec_vld spdif_aes3_transmitter_tb.dec_usr spdif_aes3_transmitter_tb.dec_ch spdif_aes3_transmitter_tb.dec_par

simvision -input simvision.tcl.svcf
