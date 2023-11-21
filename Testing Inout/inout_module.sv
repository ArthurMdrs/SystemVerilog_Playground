typedef enum logic {IS_INPUT, IS_OUTPUT} port_state_t;

module stub (
  inout wire  [7:0] io_port,
  input logic [7:0] data,
  input port_state_t port_state
);
  
  logic [7:0] internal_var;
  
  always_comb
    unique case (port_state)
      IS_INPUT : internal_var = 'z;
      IS_OUTPUT: internal_var = data;
    endcase
  
  assign io_port = internal_var;
  
  // Alternative code without internal variable:
  //assign io_port = (port_state == IS_OUTPUT) ? data : 'z ;
  
endmodule
