
PKG = ../rtl/pkg/*.sv
RTL = ../rtl/*.sv
TB = ./*.sv
TOP = -top spdif_aes3_transmitter_tb

SEED = random

run: sim

sim:
	xrun -64bit -sv -timescale 1ns/1ps $(PKG) $(TB) $(RTL) $(TOP) \
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM

gui:
	xrun -64bit -sv -timescale 1ns/1ns $(PKG) $(TB) $(RTL) $(TOP) \
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM \
		 -gui -input simvision.tcl

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~
