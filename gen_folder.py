import sys
import os
import shutil

# folder_name = sys.argv[1]
if len(sys.argv) > 1:
    folder_name = sys.argv[1]
else:
    folder_name = "New Folder"

if len(sys.argv) > 2:
    design_name = sys.argv[2]
else:
    design_name = "stub"
    
module_str = f'''module {design_name} #(
    
) (
    
);
    
    
    
endmodule
'''

tb_str = f'''module {design_name}_tb;

// Specifying time units for the simulation
timeunit 1ns;
timeprecision 1ps;

// Import packages
// import {design_name}_pkg::*;

// DUT parameters

// DUT signals

// The DUT
{design_name} #(
    
) dut (
    
);

// Simulation variables
int n_mismatches;
bit verbose = 0;

// Clock 
localparam int PERIOD = 2;
localparam int MAX_CYCLES = 10_000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    // forever #(PERIOD/2) clk = ~clk;
    $display ("\\nSimulation reached the time limit. Terminating simulation.\\n");
    $finish;
end

// The proccess
initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 6); // e.g.: " 900ns"

    $display("#==========================================================#");
    
    reset ();
    

    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

    $display("#==========================================================#");
    $finish;
end

//=============== Tasks and Functions - Begin ===============//

task reset ();
    rst_n = 1;
    @(negedge clk) rst_n = 0;
    @(negedge clk) rst_n = 1;
    $display("%t: Reset done.", $realtime);
endtask

task checkit (int expected, int actual);
    if (expected != actual) begin
        $display("%t: ERROR! Expected = %0d. Actual = %0d.", $time, expected, actual);
        n_mismatches++;
    end
endtask

//=============== Tasks and Functions - End ===============//

endmodule'''

makefile_str = f'''
#PKG = ../rtl/pkg/*.sv
RTL = ../rtl/*.sv
TB = ./*.sv
TOP = -top {design_name}_tb

SEED = 1

run: sim

sim:
	xrun -64bit -sv -timescale 1ns/1ps $(PKG) $(TB) $(RTL) $(TOP) \\
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM

gui:
	xrun -64bit -sv -timescale 1ns/1ns $(PKG) $(TB) $(RTL) $(TOP) \\
		 -access +rwc +SVSEED=$(SEED) +define+SVA_ON +define+SIM \\
		 -gui -input simvision.tcl

clean:
	rm -rf xcelium.d INCA_libs xrun.* *.shm *.dsn *.trn *.ucm ncvlog_*.err imc.key .simvision jgproject
	rm -r  mapped* rc* fv libscore_work script *.log *.history log/* png/* *.diag *.so *.sig~
'''



os.makedirs(folder_name+"/rtl", exist_ok=True)
os.makedirs(folder_name+"/tb", exist_ok=True)
# os.makedirs(folder_name+"/fv", exist_ok=True)
# os.makedirs(folder_name+"/py_scripts", exist_ok=True)

with open(folder_name+"/README", 'w') as file:
    file.write("Readme.")
with open(folder_name+"/rtl/"+design_name+".sv", 'w') as file:
    file.write(module_str)
with open(folder_name+"/tb/"+design_name+"_tb.sv", 'w') as file:
    file.write(tb_str)
# shutil.copy("Waveform Generator/tb/runme.sh", folder_name+"/tb/runme.sh")
with open(folder_name+"/tb/Makefile", 'w') as file:
    file.write(makefile_str)

print("Created folder \""+folder_name+"\" with design named \""+design_name+"\".")
