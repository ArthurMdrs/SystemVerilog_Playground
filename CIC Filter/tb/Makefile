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
# JG_SCRIPT = tcl/jg_decimator.tcl
JG_SCRIPT = tcl/jg_CIC_filter.tcl

SEED = 1

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
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject python/__pycache__
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so 

many: 
	@for i in 1 2 3 4 5 6 ; do \
		for j in 2 4 8; do \
			# echo $${i}; \
			# cp xrun.log logs/$${i}.log; \
			echo "localparam int WIDTH = 8;" > params.sv; \
			echo "localparam int STAGES = $${i};" >> params.sv; \
			echo "localparam int RATE = $${j};" >> params.sv; \
			xrun -64bit -sv $(VERIF) $(RTL) $(SVA) $(TOP) \
				-timescale 1ns/1ns -access +rwc +SVSEED=$(SEED) $(GUI) \
				-l logS$${i}R$${j}.log; \
			python3 python/plot.py $${i} $${j}; \
		done \
	done
	@mv -f *.log ./log/
	@mv -f *.history ./log/
