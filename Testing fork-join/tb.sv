`default_nettype none

module tb;

  // Specifying time units for the simulation
  timeunit 1ns;
  timeprecision 1ps;
  
  // Variables used in the simulation
  int a = 10, b = 10; 
  
  // Simulation
  initial begin
    // Creating .vcd for waveform visualization
    $dumpfile("dump.vcd"); 
	$dumpvars;
  	// Specifying %t format
    $timeformat(-9, 3, "ns", 9); 
    
    $display("***********************************************************");
    $display("********             SIMULATION START              ********");
    $display("***********************************************************");
      
    $display("  join: waits for all threads to end before moving on.");    
    fork
      espera_b;
      #4ns b = -20;
    join
    $display("Expected result: time = 4ns and b = -20.");
    $display("%t: Left fork-join. a = %0d, b = %0d", $realtime, a, b);
    
    $display("\n  join_none: does not wait for any thread to end before moving on.");
    fork
      #2ns a = 1;
      #3ns b = 2;
    join_none
    $display("Expected result: a and b keep their previous values.");
    $display("%t: Left fork-join_none. a = %0d, b = %0d.", $realtime, a, b);
    #4ns;
    $display("%t: After some delay: a = %0d, b = %0d.", $realtime, a, b);
    
    
    $display("\n  join_any: waits for only one thread to end before moving on."); 
    fork
      #2ns a = 3;
      #3ns b = 4;
    join_any
    $display("Expected result: a changed, b did not.");
    $display("%t: Left fork-join_any. a = %0d, b = %0d.", $realtime, a, b);
    #2ns;
    $display("%t: After some delay: a = %0d, b = %0d.", $realtime, a, b);
    
    $display("***********************************************************");
    $display("********              SIMULATION END               ********");
    $display("***********************************************************");  
    
    $finish;
  end 
  
  
  task espera_b;
    wait (b);
  endtask
    
endmodule

