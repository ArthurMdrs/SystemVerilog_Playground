
PKG= ../rtl/pkg/*.sv
RTL = ../rtl/*.sv
TB = ./*.sv
TOP = -top i2s_transmitter_tb

SEED = 1

run: sim

sim:
	xrun -64bit -sv $(PKG) $(TB) $(RTL) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) $(GUI)

gui:
	xrun -64bit -sv $(PKG) $(TB) $(RTL) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) -gui -input simvision.tcl

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~
