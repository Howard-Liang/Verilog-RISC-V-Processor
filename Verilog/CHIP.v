// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;  //  0: Read data from data/stack memory 1: Write data to data/stack memory
    output [31:0] mem_addr_D ;  //  Address of data/stack memory
    output [31:0] mem_wdata_D;  //  Data written to data/stack memory
    input  [31:0] mem_rdata_D;  //  Data read from data/stack memory
    // For mem_I
    output [31:0] mem_addr_I ;  //  Address of instruction (text) memory
    input  [31:0] mem_rdata_I;  //  Instruction read from instruction (text) memory
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg    [31:0] PC_nxt      ;              //
    reg           regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg    [31:0] rd_data     ;              //
    //---------------------------------------//


    // *** It seems like rs1, rs2, rd should be fetched by our own. *** //
    assign rs1 = mem_rdata_I[19:15];
    assign rs2 = mem_rdata_I[24:20];
    assign rd  = mem_rdata_I[11: 7];

    // Todo: other wire/reg
    wire        mode               ;  // %%% DIV or MUL %%% //
    wire        valid              ;  // %%% When mulDiv received signal, output 1 %%% //
    reg         CAL,CAL_nxt        ;  
    reg         stay               ;  // %%% If (stay and !ready), PC=PC_nxt %%% //
    reg         Jump               ;  // *** If (jal or jalr), jump = 1, otherwise, jump = 0 *** //
    reg         Branch             ;  // *** If the instruction is beq_BNE, Branch = 1. *** //
    reg         mem_wen_D          ;  // *** 0 for MemRead, 1 for MemWrite. *** //     ???
    reg         MemtoReg           ;  // *** MUX for Reg write data *** //
    reg  [ 1:0] ALUOp              ;  // *** Part of the control signal for ALU. *** //
    reg         ALUSrc             ;  // *** MUX for ALU source. *** //
    wire        ALUZERO            ;  // *** If rs1==rs2, ALUZERO = 1. *** //
    reg  [31:0] Imm_Gen_out        ;  // *** Imm_Gen gets instruction as input, this wire is the Imm_Gen output. *** //
    reg  [ 3:0] ALUctl             ;  // *** 4 bits signal indicating ALU operation *** //
    reg  [31:0] ALUin1             ;  // *** First input for ALU *** //
    reg  [31:0] ALUin2             ;  // *** Second input for ALU *** //
    reg  [31:0] temp_write_data    ;  // *** For regWrite MUX *** //
    wire [31:0] ALUOut             ;  // *** Output of the ALU *** //
    wire [63:0] mulDivout          ;  // %%% Output of the mulDiv %%% //
    wire        ready              ;  // %%% When mulDiv finished, output 1 %%% //
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    
    // Todo: any combinational/sequential circuit
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end


    // *** Implement Control case by case. *** //

    // --- parameters for instruction opcode --- //
    parameter BEQ_BNE = 99;  // 99 = 7'b1100011
    parameter ADD_SUB_MUL_DIV = 51;  // 51 = 7'b0110011
    parameter LW = 3;  // 3 = 7'b0000011
    parameter SW = 35;  // 35 = 7'b0100011
    parameter ADDI_SLTI_SLLI_SRLI = 19;  // 19 = 7'b0010011
    parameter AUIPC = 23;  // 23 = 7'b0010111
    parameter JAL = 111;  // 111 = 7'b1101111
    parameter JALR = 103;  // 103 = 7'b1100111
    // parameter MUL_DIV = 51;  // 51 = 7'b0110011;

    // --- Control --- //
    always @(*) begin
        case(mem_rdata_I[6:0])
            BEQ_BNE: begin
                Jump      = 1'b0 ;
                Branch    = 1'b1 ;
                mem_wen_D = 1'b0 ;   // ???
                MemtoReg  = 1'b0 ;   // ???
                ALUOp     = 2'b01;
                ALUSrc    = 1'b0 ;
                regWrite  = 1'b0 ;
                stay      = 1'b0 ;
            end
            ADD_SUB_MUL_DIV: begin
                if (mem_rdata_I[25] == 1) begin   // *** MUL *** //
                    Jump      = 1'b0 ;   // Don't care
                    Branch    = 1'b0 ;   // Don't care
                    mem_wen_D = 1'b0 ;   // Don't care
                    MemtoReg  = 1'b0 ;   // Don't care
                    ALUOp     = 2'b00;   // Don't care
                    ALUSrc    = 1'b0 ;   // Don't care
                    regWrite  = (ready) ? 1'b1 : 1'b0 ;   
                    stay      = 1'b1 ;  
                end
                else begin                        // *** ADD_SUB *** //
                    Jump      = 1'b0 ;
                    Branch    = 1'b0 ;
                    mem_wen_D = 1'b0 ;   // ???
                    MemtoReg  = 1'b0 ;   // ???
                    ALUOp     = 2'b10;
                    ALUSrc    = 1'b0 ;
                    regWrite  = 1'b1 ;
                    stay      = 1'b0 ;
                end
            end
            LW: begin
                Jump      = 1'b0 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b1 ;
                ALUOp     = 2'b00;
                ALUSrc    = 1'b1 ;
                regWrite  = 1'b1 ;
                stay      = 1'b0 ;
            end
            SW: begin
                Jump      = 1'b0 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b1 ;
                MemtoReg  = 1'b0 ;   // Don't care
                ALUOp     = 2'b00;
                ALUSrc    = 1'b1 ;
                regWrite  = 1'b0 ;
                stay      = 1'b0 ;
            end
            ADDI_SLTI_SLLI_SRLI: begin
                Jump      = 1'b0 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b0 ;
                ALUOp     = 2'b11;   // may be change
                ALUSrc    = 1'b1 ;
                regWrite  = 1'b1 ;
                stay      = 1'b0 ;
            end
            AUIPC: begin
                Jump      = 1'b0 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b0 ;
                ALUOp     = 2'b00;   // *** I think definitely add should be ok ***
                ALUSrc    = 1'b1 ;
                regWrite  = 1'b1 ;
                stay      = 1'b0 ;
            end
            JAL: begin
                Jump      = 1'b1 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b0 ;   // Don't care
                ALUOp     = 2'b00;   // Don't care
                ALUSrc    = 1'b0 ;   // Don't care
                regWrite  = 1'b1 ;
                stay      = 1'b0 ;
            end
            JALR: begin
                Jump      = 1'b1 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b0 ;   // Don't care
                ALUOp     = 2'b00;   // *** I think definitely add should be ok ***
                ALUSrc    = 1'b1 ;   
                regWrite  = 1'b1 ;
                stay      = 1'b0 ;
            end
            // MUL_DIV: begin
            //     Jump      = 1'b0 ;   // Don't care
            //     Branch    = 1'b0 ;   // Don't care
            //     mem_wen_D = 1'b0 ;   // Don't care
            //     MemtoReg  = 1'b0 ;   // Don't care
            //     ALUOp     = 2'b00;   // Don't care
            //     ALUSrc    = 1'b0 ;   // Don't care
            //     regWrite  = 1'b1 ;   
            //     stay      = 1'b1 ;   
            // end
            default: begin
                Jump      = 1'b0 ;
                Branch    = 1'b0 ;
                mem_wen_D = 1'b0 ;
                MemtoReg  = 1'b0 ;
                ALUOp     = 2'b00;
                ALUSrc    = 1'b0 ;
                regWrite  = 1'b0 ;
                stay      = 1'b0 ;
            end
        endcase
    end
    // *** Implement Control case by case. *** //


    // *** Implement Imm_Gen output *** //
    always @(*) begin
        case(mem_rdata_I[6:0])
            BEQ_BNE: begin
                Imm_Gen_out[31:13] = {19{mem_rdata_I[31:31]}};
                Imm_Gen_out[12:12] = mem_rdata_I[31:31];
                Imm_Gen_out[11:11] = mem_rdata_I[ 7: 7];
                Imm_Gen_out[10: 5] = mem_rdata_I[30:25];
                Imm_Gen_out[ 4: 1] = mem_rdata_I[11: 8];
                Imm_Gen_out[ 0: 0] = 1'd0;
            end
            ADD_SUB_MUL_DIV: begin
                Imm_Gen_out = 32'd0;   // ???
            end
            LW: begin
                Imm_Gen_out[31:12] = {20{mem_rdata_I[31:31]}};
                Imm_Gen_out[11: 0] = mem_rdata_I[31:20];
            end
            SW: begin
                Imm_Gen_out[31:12] = {20{mem_rdata_I[31:31]}};
                Imm_Gen_out[11: 5] = mem_rdata_I[31:25];
                Imm_Gen_out[ 4: 0] = mem_rdata_I[11: 7];
            end
            ADDI_SLTI_SLLI_SRLI: begin
                if ( (mem_rdata_I[14:12] == 3'b000) | (mem_rdata_I[14:12] == 3'b010) ) begin       // *** if True => addi or slti *** //
                    Imm_Gen_out[31:12] = {20{mem_rdata_I[31:31]}};
                    Imm_Gen_out[11: 0] = mem_rdata_I[31:20];
                end
                else begin
                    Imm_Gen_out[31: 5] = 27'd0;
                    Imm_Gen_out[ 4: 0] = mem_rdata_I[24:20];            // *** else slli or srli *** //
                end
            end
            AUIPC: begin
                Imm_Gen_out[31:12] = mem_rdata_I[31:12];
                Imm_Gen_out[11: 0] = 12'd0;
            end
            JAL: begin
                Imm_Gen_out[31:21] = {11{mem_rdata_I[31:31]}};
                Imm_Gen_out[20:20] = mem_rdata_I[31:31];
                Imm_Gen_out[19:12] = mem_rdata_I[19:12];
                Imm_Gen_out[11:11] = mem_rdata_I[20:20];
                Imm_Gen_out[10: 1] = mem_rdata_I[30:21];
                Imm_Gen_out[ 0: 0] = 1'd0;
            end
            JALR: begin
                Imm_Gen_out[31:12] = {20{mem_rdata_I[31:31]}};
                Imm_Gen_out[11: 0] = mem_rdata_I[31:20];
            end
            // MUL_DIV: begin
            //     Imm_Gen_out = 32'd0;
            // end
            default: begin
                Imm_Gen_out = 32'd0;
            end
        endcase
    end
    // *** Implement Imm_Gen output *** //


    // *** Definition on where will PC go. *** //
    always @(*) begin
        if ( ( (ALUZERO ^ mem_rdata_I[12]) & Branch ) | ( Jump & (!ALUSrc) ) ) begin
            PC_nxt = PC + Imm_Gen_out;
        end
        else if(Jump & ALUSrc)begin// %%% JALR %%% //
            PC_nxt = ALUOut;
        end
        else if( stay ) begin
            PC_nxt = (ready) ? ( PC + 32'd4 ) : PC;// %%% MUL_DIV %%% //
        end
        else begin
            PC_nxt = PC + 32'd4;
        end
    end
    // *** Definition on where will PC go. *** //


    // *** ALU control *** //
    always @(*) begin
        case(ALUOp)
            0: begin
                ALUctl = 4'b0010;
            end
            1: begin
                ALUctl = 4'b0110;
            end
            2: begin
                if (mem_rdata_I[30:30] == 1'b0) begin
                    ALUctl = 4'b0010;                       // for add and sub, their opcode are the same
                end                                         // we check if (instruction[30:30] == 0), True => add, False => sub
                else begin
                    ALUctl = 4'b0110;
                end
            end
            3: begin
                if (mem_rdata_I[14:12] == 3'b000) begin
                    ALUctl = 4'b0010;                       // for addi and slti, their opcode are the same 
                end                                         // we check if (funct3 == 000), True => addi
                else if (mem_rdata_I[14:12] == 3'b001) begin
                    ALUctl = 4'b1000;                       // *** ALUctl = 8 for shift left *** //
                end
                else if (mem_rdata_I[14:12] == 3'b101) begin
                    ALUctl = 4'b1001;                       // *** ALUctl = 9 for shift right *** //
                end
                else begin                                  // all False => slti
                    ALUctl = 4'b0111;
                end
            end
            default: begin
                ALUctl = 4'b1111;
            end
        endcase
    end
    // *** ALU control *** //


    // *** Defining the MUX for ALU input 2 *** //
    always @(*) begin
        if (ALUSrc ) begin
            ALUin2 = Imm_Gen_out;
        end
        else begin
            ALUin2 = rs2_data;
        end
    end
    // *** Defining the MUX for ALU input 2 *** //


    // *** Defining the MUX for ALU input 2 *** //
    always @(*) begin
        if (mem_rdata_I[6:0] == 7'd23) begin  // detecting for auipc
            ALUin1 = PC;
        end
        else begin
            ALUin1 = rs1_data;
        end
    end
    // *** Defining the MUX for ALU input 2 *** //


    // *** Connecting ALU's wire *** //
    ALU ALUnit(
        .ALUctl(ALUctl),
        .A(ALUin1),
        .B(ALUin2),
        .ALUOut(ALUOut),
        .Zero(ALUZERO)
    );
    // *** Connecting ALU's wire *** //


    // %%% valid &&  CAL %%% //
    assign valid = ( (!CAL) & stay );  
    always @(*) begin
        case(CAL)
        0:CAL_nxt = (stay) ? 1 : 0 ;
        1:CAL_nxt = (ready) ? 0 : 1 ;
        endcase
    end
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            CAL <= 0;
        end
        else begin
            CAL <= CAL_nxt;
        end
    end
    // %%% valid %%% //


    // %%% mode %%% //
    // assign mode = (mem_rdata_I[14]==1) ? 1 : 0 ;  // MUL when mem_rdata_I[14]=1, DIV when mem_rdata_I[14]=0 //
    assign mode = 0;
    // %%% mode %%% //


    // %%% Connecting mulDiv's wire %%% //
    mulDiv mulDivunit(
        .clk(clk), 
        .rst_n(rst_n), 
        .valid(valid), 
        .ready(ready), 
        .mode(mode), 
        .in_A(rs1_data), 
        .in_B(rs2_data), 
        .out(mulDivout)
    );
    // %%% Connecting mulDiv's wire %%% //


    // *** Defining the MUX for regWrite (Jump included) (stay included) *** //
    always @(*) begin
        temp_write_data = (MemtoReg) ? mem_rdata_D : ALUOut;    
        if(Jump) rd_data = PC + 4 ;
        else if(stay) rd_data = mulDivout[31:0] ;
        else rd_data = temp_write_data ;
    end
    // *** Defining the MUX for regWrite (Jump included) (stay included) *** //


    // *** assigning output *** //
    // output        mem_wen_D  ;
    reg [31:0] mem_addr_D ;
    reg [31:0] mem_wdata_D;
    reg [31:0] mem_addr_I ;

    always @(*) begin
        mem_addr_D = ALUOut ;  
        mem_wdata_D = rs2_data;  
        mem_addr_I = PC;
    end
    // *** assigning output *** //

endmodule


module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule


// *** ALU *** //
module ALU(ALUctl, A, B, ALUOut, Zero);

    input [ 3: 0] ALUctl;
    input [31: 0] A, B  ;
    output[31: 0] ALUOut;
    output        Zero  ;
    assign Zero = (ALUOut==0);

    reg [31:0] ALUOut;

    reg signed [31:0] signA, signB;

    always @(*) begin
        signA = A;
        signB = B;
        case(ALUctl)
            // 0 : ALUOut = A & B;
            // 1 : ALUOut = A | B;
            2 : ALUOut = signA + signB;
            6 : ALUOut = A - B;
            7 : ALUOut = (A < B) ? 1 : 0;
            8 : ALUOut = A << B[4:0];
            9 : ALUOut = A >> B[4:0];
            // 12: ALUOut = ~(A | B);
            default: ALUOut = 0;
        endcase
    end

endmodule
// *** ALU *** //


// *** mulDiv submodule *** //
module mulDiv( clk, rst_n, valid, ready, mode, in_A, in_B, out);

    // Definition of ports
    input         clk, rst_n;
    input         valid, mode; // mode: 0: mulu, 1: divu
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 2'b00;
    parameter MUL  = 2'b01;
    parameter DIV  = 2'b10;
    parameter OUT  = 2'b11;

    // Todo: Wire and reg if needed
    reg  [ 1:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    wire [ 0:0] ready;
    wire [63:0] out;
    assign ready = (state == OUT) ? 1'b1 : 1'b0;
    assign out = shreg;
    
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if　(!valid) begin
                    state_nxt = IDLE;
                end
                else begin
                    state_nxt = (mode) ? DIV : MUL;
                end
            end
            MUL: begin
                state_nxt = (counter == 5'd31) ? OUT : MUL;
            end
            DIV: begin
                state_nxt = (counter == 5'd31) ? OUT : DIV;
            end
            OUT: begin
                state_nxt = IDLE;
            end
            default: begin
                state_nxt = state;
            end
        endcase
    end

    // Todo 2: Counter
    always @(*) begin
        case(state)
            IDLE: begin
                counter_nxt = 5'd0;
            end
            MUL: begin
                counter_nxt = counter + 5'd1;
            end
            DIV: begin
                counter_nxt = counter + 5'd1;
            end
            OUT: begin
                counter_nxt = 5'd0;
            end
        endcase
    end
    
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT: alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            IDLE: begin
                alu_out = 33'd0;
            end
            MUL: begin
                alu_out = (shreg[0:0] == 1'b1) ? (shreg[63:32] + alu_in) : shreg[63:32];
            end
            DIV: begin
                alu_out = (shreg[62:31] >= alu_in) ? (shreg[62:31] - alu_in) : shreg[62:31];
            end
        default begin
            alu_out = 33'd0;
        end
        endcase
    end
    
    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    shreg_nxt[31:0] = in_A;
                    shreg_nxt[63:32] = 32'd0;
                end
                else       shreg_nxt = 64'd0;
            end
            MUL: begin
                shreg_nxt[30:0] = shreg[31:1];
                shreg_nxt[63:31] = alu_out;
            end
            DIV: begin
                shreg_nxt[0:0] = (shreg[62:31] >= alu_in) ? 1'b1 : 1'b0;
                shreg_nxt[31:1] = shreg[30:0];
                shreg_nxt[63:32] = alu_out[31:0];
            end
            OUT: shreg_nxt = 64'd0;
            default: shreg_nxt = shreg;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 5'd0;
            shreg <= 64'd0;
            alu_in <= 32'd0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            shreg <= shreg_nxt;
            alu_in <= alu_in_nxt;
        end
    end

endmodule
// *** mulDiv submodule *** //