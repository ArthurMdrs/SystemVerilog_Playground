module scoreboard import T_bird_tail_light_FSM_pkg::*; (
    input  state_t state
);

    // Associative array for storing state occurences
    int state_track [state_t];

    // Initializing array
    state_t aux = aux.first();
    initial begin
        while (aux != aux.last()) begin
            state_track[aux] = 0;
            aux = aux.next();
        end
        state_track[aux] = 0;
        // foreach(state_track[i])
        //     $display("state_track[%s] = %0d", i.name(), state_track[i]);
    end

    // Count occurences logic
    always @ (state) begin
        state_track[state]++;
    end

    // Report results at the end of simulation
    final begin
        $display("####  SCOREBOARD REPORT  ####");
        foreach(state_track[i])
            $display("state_track[%s] = %0d", i.name(), state_track[i]);
    end

endmodule