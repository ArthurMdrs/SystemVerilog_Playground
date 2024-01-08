# SVA = +define+SVA_SMLBLK=1
SVA = +define+SVA_BIGBLK=1
# SVA = 

RTL = ../rtl/*.sv
VERIF = ./*.sv
TOP = -top CIC_filter_tb

# GUI = -gui
GUI =

# JG_MODE = 
# JG_MODE = -xprop
# JG_MODE = -superlint

# JG_SCRIPT = tcl/jg_comb.tcl
# JG_SCRIPT = tcl/jg_integrator.tcl
# JG_SCRIPT = tcl/jg_decim_or_interp.tcl
JG_SCRIPT = tcl/jg_CIC_filter.tcl

SEED = 1

WIDTH = 8
STAGES = 3
RATE = 8
DnI = 1
# DnI: decimator = 1, interpolator = 0

run: genwave sim plot

genwave:
	@python3 python/gen_inputs.py $(DnI) $(STAGES) $(RATE)

plot:
	@python3 python/plot.py $(DnI) $(STAGES) $(RATE)

sim:
	@echo "localparam int WIDTH = $(WIDTH);" > params.sv
	@echo "localparam int STAGES = $(STAGES);" >> params.sv
	@echo "localparam int RATE = $(RATE);" >> params.sv
	@echo "localparam bit DnI = $(DnI);" >> params.sv
	xrun -64bit -sv $(VERIF) $(RTL) $(SVA) $(TOP) \
		 -timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) $(GUI)

formal:
	jg $(JG_MODE) $(JG_SCRIPT)

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject python/__pycache__
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~

many: 
	@for i in 1 3 5 ; do \
		for j in 4 8 16 ; do \
			# echo $${i}; \
			# cp xrun.log logs/$${i}.log; \
			echo "localparam int WIDTH = 8;" > params.sv; \
			echo "localparam int STAGES = $${i};" >> params.sv; \
			echo "localparam int RATE = $${j};" >> params.sv; \
			echo "localparam bit DnI = $(DnI);" >> params.sv; \
			xrun -64bit -sv $(VERIF) $(RTL) $(SVA) $(TOP) \
				-timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) $(GUI) \
				-l logS$${i}R$${j}.log; \
			python3 python/plot.py $(DnI) $${i} $${j}; \
		done \
	done
	@mv -f *.log ./log/
	@mv -f *.history ./log/
