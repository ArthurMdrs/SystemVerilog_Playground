CP_FILES = "../../Frequency Generator/clk_gen.sv"
PKG = ../rtl/pkg/*.sv
RTL = ../rtl/*.sv
TB = ./*.sv
TOP = -top waveform_gen_tb

SEED = 1

run: cp sim

sim: cp
	xrun -64bit -sv $(PKG) $(TB) $(RTL) $(TOP) \
		 -timescale 1ns/1ps -access +rwc +SVSEED=$(SEED)

gui:
	xrun -64bit -sv $(PKG) $(TB) $(RTL) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) -gui -input simvision.tcl

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~

cp: 
	cp $(CP_FILES) ../rtl