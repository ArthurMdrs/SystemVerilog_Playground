typedef struct packed {
    logic [5:0] opcode;
    logic [4:0] rs;
    logic [4:0] rt;
    logic [4:0] rd;
    logic [4:0] shamt;
    logic [5:0] funct;
} R_inst;

typedef struct packed {
    logic [5:0] opcode;
    logic [4:0] rs;
    logic [4:0] rt;
    logic [15:0] imm;
} I_inst;

typedef struct packed {
    logic [5:0] opcode;
    logic [25:0] addr;
} J_inst;

typedef union packed {
    R_inst R;
    I_inst I;
    J_inst J;
} inst;

module MIPS_Instructions;

    inst a;

    initial begin

        assert(randomize(a));

        $display("#==========================================================#");

        $display("The instruction in R format is:");
        $display("opcode_rs_rt_rd_shamt_funct");
        $display("%b_%b_%b_%b_%b_%b", a.R.opcode, a.R.rs, a.R.rt, a.R.rd, a.R.shamt, a.R.funct);

        $display("The instruction in I format is:");
        $display("opcode_rs_rt_imm");
        $display("%b_%b_%b_%b", a.I.opcode, a.I.rs, a.I.rt, a.I.imm);

        $display("The instruction in J format is:");
        $display("opcode_addr");
        $display("%b_%b", a.J.opcode, a.J.addr);

        $display("#==========================================================#");

    end

endmodule