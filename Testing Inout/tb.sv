`default_nettype none

module tb;

  // Specifying time units for the simulation
  timeunit 1ns;
  timeprecision 1ps;
  
  // Variables used in the simulation
  int a = 10, b = 10;
  // Variables used in the DUTs
  port_state_t port_state_1, port_state_2;
  wire  [7:0] io_port;
  logic [7:0] data;
  // DUTs
  stub dut1 (.data, .io_port, .port_state(port_state_1));
  stub dut2 (.data, .io_port, .port_state(port_state_2));
  
  // Stimulus generation
  initial begin
    // Creating .vcd for waveform visualization
    $dumpfile("dump.vcd"); 
	$dumpvars;
  	// Specifying %t format
    $timeformat(-9, 3, "ns", 9);
    
    $display("***********************************************************");
    $display("********             SIMULATION START              ********");
    $display("***********************************************************");
    
    $display("Case 1: DUT 1 sends to DUT 2");
    port_state_1 = IS_OUTPUT;
    port_state_2 = IS_INPUT ;
    data = 10;
    #1 data = 20;
    #1 data = 30;    
    #1;
    
    $display("Case 2: DUT 2 sends to DUT 1");
    port_state_1 = IS_INPUT ;
    port_state_2 = IS_OUTPUT;
    data = 10;
    #1 data = 20;
    #1 data = 30;  
    #1;
    
    $display("***********************************************************");
    $display("********              SIMULATION END               ********");
    $display("***********************************************************");  
    
    $finish;
  end
  
  // Debug
  always @ (dut1.internal_var, dut2.internal_var)
    $display("%t: Internal variable value: DUT 1 = %0d, DUT 2 = %0d.", 
             $realtime, dut1.internal_var, dut2.internal_var);
    
endmodule

