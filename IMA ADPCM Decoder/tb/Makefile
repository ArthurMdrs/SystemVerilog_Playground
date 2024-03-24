
#PKG = ../rtl/pkg/*.sv
RTL = ../rtl/*.sv
TB = ./*.sv
TOP = -top ima_adpcm_decoder_tb

SEED = 1

run: sim

sim:
	xrun -64bit -sv -timescale 1ns/1ps $(PKG) $(TB) $(RTL) $(TOP) \
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM

gui:
	xrun -64bit -sv -timescale 1ns/1ns $(PKG) $(TB) $(RTL) $(TOP) \
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM \
		 -gui -input simvision.tcl

clean:
	@rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject 2> /dev/null || true
	@rm -rf mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~ 2> /dev/null || true
