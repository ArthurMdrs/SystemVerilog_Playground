# SVA = +define+SVA_ENABLE=1
SVA = 

RTL = ../rtl/*.sv
VERIF = ./*.sv
TOP = -top CIC_filter_tb

# GUI = -gui
GUI =

# JG_MODE = 
# JG_MODE = -xprop
# JG_MODE = -superlint

# JG_SCRIPT = jg_comb.tcl
# JG_SCRIPT = jg_integrator.tcl
# JG_SCRIPT = jg_decimator.tcl
JG_SCRIPT = jg_CIC_filter.tcl

SEED = random

run: genwave sim plot

genwave:
	python3 python/gen_inputs.py

plot:
	python3 python/plot.py

sim:
	xrun -64bit -sv $(VERIF) $(RTL) $(SVA) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) $(GUI)

formal:
	jg $(JG_MODE) $(JG_SCRIPT)

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision *.log *.diag *.so jgproject python/__pycache__
	rm -r  mapped* rc* fv libscore_work script
