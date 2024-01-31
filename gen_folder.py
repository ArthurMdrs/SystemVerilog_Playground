import sys
import os
import shutil

folder_name = sys.argv[1]

if len(sys.argv) > 2:
    design_name = sys.argv[2]
else:
    design_name = "stub"

module_str  = "module "+design_name+" #(\n"
module_str += "    \n"
module_str += ") (\n"
module_str += "    \n"
module_str += ");\n"
module_str += "\n\n\n"
module_str += "endmodule\n"

tb_str = f'''module {design_name}_tb;

// Specifying time units for the simulation
timeunit 1ns;
timeprecision 1ps;

// Import packages
// import {design_name}_pkg::*;

// DUT parameters

// DUT signals

// The DUT

// Simulation variables
int n_mismatches;
bit verbose = 0;

// Clock 
localparam int PERIOD = 2;
localparam int MAX_CYCLES = 10_000;
initial begin
    clk = 0; 
    // repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    forever #(PERIOD/2) clk = ~clk;
    $display ("\nSimulation reached the time limit. Terminating simulation.\n");
    $finish;
end

// The proccess
initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 6); // e.g.: " 900ns"

    $display("#==========================================================#");
    
    reset ();
    

    $display("%t: Simulation end.", $time);

    $display("#==========================================================#");
    $finish;
end

//=============== Tasks and Functions - Begin ===============//

task reset ();
    rst_n = 0;
    #3 rst_n = 1;
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

os.makedirs(folder_name+"/rtl", exist_ok=True)
os.makedirs(folder_name+"/tb", exist_ok=True)
os.makedirs(folder_name+"/fv", exist_ok=True)
os.makedirs(folder_name+"/py_scripts", exist_ok=True)

with open(folder_name+"/rtl/"+design_name+".sv", 'w') as file:
    file.write(module_str)
with open(folder_name+"/tb/"+design_name+"_tb.sv", 'w') as file:
    file.write(tb_str)
shutil.copy("Waveform Generator/tb/runme.sh", folder_name+"/tb/runme.sh")

print("Created folder \""+folder_name+"\" with design named \""+design_name+"\".")
