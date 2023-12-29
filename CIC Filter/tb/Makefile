# SVA = +define+SVA_ENABLE=1
SVA = 

RTL = ../rtl/*.sv
VERIF = ./*.sv
TOP = -top CIC_filter_tb

# JG_MODE = 
# JG_MODE = -xprop
# JG_MODE = -superlint

# JG_SCRIPT = jg_comb.tcl
# JG_SCRIPT = jg_integrator.tcl
# JG_SCRIPT = jg_decimator.tcl
JG_SCRIPT = jg_CIC_filter.tcl

SEED = random

run: all

all:
	xrun -64bit -sv $(VERIF) $(RTL) $(SVA) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED)

formal:
	jg $(JG_MODE) $(JG_SCRIPT)

sim: all 

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision *.log *.diag *.so jgproject
	rm -r  mapped* rc* fv libscore_work script