/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_pipe_idu.sv>
/// @brief      Instruction Decoder Unit (IDU)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Decodes the instruction and creates the appropriate control signals for EXU
 //
 // Structure:
 // - Instruction decoder
 // - IDU <-> IFU i/f
 // - IDU <-> EXU i/f
 //
//------------------------------------------------------------------------------

`include "scr1_memif.svh"
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_arch_description.svh"

module scr1_pipe_idu
(
`ifdef SCR1_TRGT_SIMULATION
    input   logic                           rst_n,                  // IDU reset
    input   logic                           clk,                    // IDU clock
`endif // SCR1_TRGT_SIMULATION

    // IFU <-> IDU interface
    output  logic                           idu2ifu_rdy_o,          // IDU ready for new data
    input   logic [`SCR1_IMEM_DWIDTH-1:0]   ifu2idu_instr_i,        // IFU instruction
    input   logic                           ifu2idu_imem_err_i,     // Instruction access fault exception
    input   logic                           ifu2idu_imem_page_err_i,     // Instruction access fault exception
    input   logic                           ifu2idu_err_rvi_hi_i,   // 1 - imem fault when trying to fetch second half of an unaligned RVI instruction
    input   logic                           ifu2idu_vd_i,           // IFU request

    // IDU <-> EXU interface
    output  logic                           idu2exu_req_o,          // IDU request
    output  type_scr1_exu_cmd_s             idu2exu_cmd_o,          // IDU command
    output  logic                           idu2exu_use_rs1_o,      // Instruction uses rs1
    output  logic                           idu2exu_use_rs2_o,      // Instruction uses rs2
    output  logic                           idu2exu_use_rs3_o,      // Instruction uses rs3
`ifndef SCR1_NO_EXE_STAGE
    output  logic                           idu2exu_use_rd_o,       // Instruction uses rd
    output  logic                           idu2exu_use_imm_o,      // Instruction uses immediate
`endif // SCR1_NO_EXE_STAGE
    input   logic                           exu2idu_rdy_i           // EXU ready for new data
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------

localparam [SCR1_GPR_FIELD_WIDTH-1:0] SCR1_MPRF_ZERO_ADDR   = 5'd0;
localparam [SCR1_GPR_FIELD_WIDTH-1:0] SCR1_MPRF_RA_ADDR     = 5'd1;
localparam [SCR1_GPR_FIELD_WIDTH-1:0] SCR1_MPRF_SP_ADDR     = 5'd2;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

logic [`SCR1_IMEM_DWIDTH-1:0]       instr;
type_scr1_instr_type_e              instr_type;
type_scr1_rvi_opcode_e              rvi_opcode;
logic                               rvi_illegal;
logic [2:0]                         funct3;
logic [5:0]                         funct6;
logic [6:0]                         funct7;
logic [11:0]                        funct12;
logic [5:0]                         shamt;
`ifdef SCR1_RVC_EXT
logic                               rvc_illegal;
`endif  // SCR1_RVC_EXT
`ifdef SCR1_RVE_EXT
logic                               rve_illegal;
`endif  // SCR1_RVE_EXT

//-------------------------------------------------------------------------------
// Instruction decoding
//-------------------------------------------------------------------------------

assign idu2ifu_rdy_o  = exu2idu_rdy_i;
assign idu2exu_req_o  = ifu2idu_vd_i;
assign instr          = ifu2idu_instr_i;

// RVI / RVC
assign instr_type   = type_scr1_instr_type_e'(instr[1:0]);

// RVI / RVC fields
assign rvi_opcode   = type_scr1_rvi_opcode_e'(instr[6:2]);                          // RVI
assign funct3       = (instr_type == SCR1_INSTR_RVI) ? instr[14:12] : instr[15:13]; // RVI / RVC
assign funct6       = instr[31:26];                                                 // RV64I
assign funct7       = instr[31:25];                                                 // RVI
assign funct12      = instr[31:20];                                                 // RVI (SYSTEM)
assign shamt        = instr[25:20];                                                 // RVI

// RV64IMAFDC decode
always_comb begin
    // Defaults
    idu2exu_cmd_o.instr_rvc   = 1'b0;
	idu2exu_cmd_o.instr_rvf	  = 1'b0;
    idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
    idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_NONE;
    idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
    idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_NONE;
	idu2exu_cmd_o.fpu_cmd	  = SCR1_FPU_CMD_NONE;
	idu2exu_cmd_o.fpu_rnd	  = SCR1_FPU_RND_RNE;
	idu2exu_cmd_o.fpu_src_fmt = SCR1_FPU_FMT_F64;
	idu2exu_cmd_o.fpu_dst_fmt = SCR1_FPU_FMT_F64;
	idu2exu_cmd_o.fpu_int_fmt = SCR1_FPU_FMT_I64;
	idu2exu_cmd_o.amo_cmd	  = SCR1_AMO_CMD_NONE;
    idu2exu_cmd_o.csr_op      = SCR1_CSR_OP_REG;
    idu2exu_cmd_o.csr_cmd     = SCR1_CSR_CMD_NONE;
    idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_NONE;
	idu2exu_cmd_o.rd_f_wb_sel = SCR1_RD_F_WB_NONE;
    idu2exu_cmd_o.jump_req    = 1'b0;
    idu2exu_cmd_o.branch_req  = 1'b0;
    idu2exu_cmd_o.mret_req    = 1'b0;
    idu2exu_cmd_o.sret_req    = 1'b0;
    idu2exu_cmd_o.fencei_req  = 1'b0;
    idu2exu_cmd_o.wfi_req     = 1'b0;
	idu2exu_cmd_o.sfence_req  = 1'b0;
    idu2exu_cmd_o.rs1_addr    = '0;
    idu2exu_cmd_o.rs2_addr    = '0;
    idu2exu_cmd_o.rs3_addr    = '0;
    idu2exu_cmd_o.rd_addr     = '0;
    idu2exu_cmd_o.imm         = '0;
    idu2exu_cmd_o.exc_req     = 1'b0;
    idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_INSTR_MISALIGN;

    // Clock gating
    idu2exu_use_rs1_o         = 1'b0;
    idu2exu_use_rs2_o         = 1'b0;
    idu2exu_use_rs3_o         = 1'b0;
`ifndef SCR1_NO_EXE_STAGE
    idu2exu_use_rd_o          = 1'b0;
    idu2exu_use_imm_o         = 1'b0;
`endif // SCR1_NO_EXE_STAGE

    rvi_illegal             = 1'b0;
`ifdef SCR1_RVE_EXT
    rve_illegal             = 1'b0;
`endif  // SCR1_RVE_EXT
`ifdef SCR1_RVC_EXT
    rvc_illegal             = 1'b0;
`endif  // SCR1_RVC_EXT

    // Check for IMEM access fault
    if (ifu2idu_imem_err_i) begin
        idu2exu_cmd_o.exc_req     = 1'b1;
        idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_INSTR_ACCESS_FAULT;
        idu2exu_cmd_o.instr_rvc   = ifu2idu_err_rvi_hi_i;
    end 
	else if (ifu2idu_imem_page_err_i) begin
        idu2exu_cmd_o.exc_req     = 1'b1;
        idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_INSTR_PAGE_FAULT;
        idu2exu_cmd_o.instr_rvc   = ifu2idu_err_rvi_hi_i;
	end
	else begin  // no imem fault
        case (instr_type)
            SCR1_INSTR_RVI  : begin
                idu2exu_cmd_o.rs1_addr    = instr[19:15];
                idu2exu_cmd_o.rs2_addr    = instr[24:20];
                idu2exu_cmd_o.rs3_addr    = instr[31:27];
                idu2exu_cmd_o.rd_addr     = instr[11:7];
                case (rvi_opcode)
                    SCR1_OPCODE_AUIPC           : begin
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_SUM2;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, instr[31:12], 12'b0};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_AUIPC

                    SCR1_OPCODE_LUI             : begin
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IMM;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, instr[31:12], 12'b0};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_LUI

                    SCR1_OPCODE_JAL             : begin
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_INC_PC;
                        idu2exu_cmd_o.jump_req    = 1'b1;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_JAL

                    SCR1_OPCODE_LOAD            : begin
                        idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_LSU;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:20]};
                        case (funct3)
                            3'b000  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LB;
                            3'b001  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LH;
                            3'b010  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LW;
                            3'b011  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LD;
                            3'b100  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LBU;
                            3'b101  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LHU;
                            3'b110  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_LWU;
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_LOAD

                    SCR1_OPCODE_LOAD_FP         : begin
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
                        idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.rd_f_wb_sel = SCR1_RD_F_WB_LSU;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:20]};
                        case (funct3)
                            3'b010  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_FLW;
                            3'b011  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_FLD;
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_LOAD_FP

                    SCR1_OPCODE_STORE           : begin
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:25], instr[11:7]};
                        case (funct3)
                            3'b000  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_SB;
                            3'b001  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_SH;
                            3'b010  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_SW;
                            3'b011  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_SD;
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[19] | instr[24])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_STORE

                    SCR1_OPCODE_STORE_FP        : begin
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:25], instr[11:7]};
                        case (funct3)
                            3'b010  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_FSW;
                            3'b011  : idu2exu_cmd_o.lsu_cmd = SCR1_LSU_CMD_FSD;
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[19] | instr[24])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_STORE_FP

                    SCR1_OPCODE_OP              : begin
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                        case (funct7)
                            7'b0000000 : begin
                                case (funct3)
                                    3'b000  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_ADD;
                                    3'b001  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SLL;
                                    3'b010  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SUB_LT;
                                    3'b011  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SUB_LTU;
                                    3'b100  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_XOR;
                                    3'b101  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SRL;
                                    3'b110  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_OR;
                                    3'b111  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_AND;
                                endcase // funct3
                            end // 7'b0000000

                            7'b0100000 : begin
                                case (funct3)
                                    3'b000  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SUB;
                                    3'b101  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SRA;
                                    default : rvi_illegal = 1'b1;
                                endcase // funct3
                            end // 7'b0100000
`ifdef SCR1_RVM_EXT
                            7'b0000001 : begin
                                case (funct3)
                                    3'b000  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_MUL;
                                    3'b001  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_MULH;
                                    3'b010  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_MULHSU;
                                    3'b011  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_MULHU;
                                    3'b100  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_DIV;
                                    3'b101  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_DIVU;
                                    3'b110  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_REM;
                                    3'b111  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_REMU;
                                endcase // funct3
                            end // 7'b0000001
`endif  // SCR1_RVM_EXT
                            default : rvi_illegal = 1'b1;
                        endcase // funct7
`ifdef SCR1_RVE_EXT
                        if (instr[11] | instr[19] | instr[24])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_OP

					SCR1_OPCODE_OP_W			: begin
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE

						idu2exu_cmd_o.ialu_op		= SCR1_IALU_OP_REG_REG;
						idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_IALU;
						case (funct7)
							7'b0000000 : begin
								case (funct3)
									3'b000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ADDW;
									3'b001	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SLLW;
									3'b101	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SRLW;
									default	: rvi_illegal = 1'b1;
								endcase // funct3
							end // 7'b0000000

							7'b0000001 : begin
								case (funct3)
									3'b000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MULW;
									3'b100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_DIVW;
									3'b101	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_DIVUW;
									3'b110	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_REMW;
									3'b111	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_REMUW;
									default	: rvi_illegal = 1'b1;
								endcase
							end // 7'b0000001

							7'b0100000 : begin
								case (funct3)
									3'b000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SUBW;
									3'b101	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SRAW;
									default	: rvi_illegal = 1'b1;
								endcase // funct3
							end // 7'b0100000

							default : rvi_illegal = 1'b1;
						endcase // funct7
					end // SCR1_OPCODE_OP_W

                    SCR1_OPCODE_OP_FP           : begin
						idu2exu_cmd_o.instr_rvf	  	= 1'b1;
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
						idu2exu_use_rs3_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o			= 1'b1;
`endif // SCR1_NO_EXE_STAGE

						case (funct3)
							3'b000	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RNE;
							3'b001	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RTZ;
							3'b010	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RDN;
							3'b011	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RUP;
							3'b100	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RMM;
							3'b111	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_DYN;
							default	: rvi_illegal = 1'b1;
						endcase // funct3

						case (funct7[1:0])
							2'b00	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F32;
							2'b01	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F64;
							default	: rvi_illegal = 1'b1;
						endcase // funct7[1:0]

						case (funct7[6:2])
							5'b00000 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FADD;
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
							end // 5'b00000

							5'b00001 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FSUB;
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
							end // 5'b00001

							5'b00010 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMUL;
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
							end // 5'b00010

							5'b00011 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FDIV;
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
							end // 5'b00011

							5'b00100 : begin
								case (funct3)
									3'b000 : begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FSGNJ;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									3'b001 : begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FSGNJN;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									3'b010 : begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FSGNJX;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									default : rvi_illegal = 1'b1;
								endcase // funct3
							end // 5'b00100

							5'b00101 : begin
								case (funct3)
									3'b000 : begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMIN;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									3'b001 : begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMAX;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									default : rvi_illegal = 1'b1;
								endcase // funct3
							end // 5'b00101

							5'b01000 : begin
								case (instr[24:20])
									5'b00000 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2F;
										idu2exu_cmd_o.fpu_src_fmt	= SCR1_FPU_FMT_F32;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									5'b00001 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2F;
										idu2exu_cmd_o.fpu_src_fmt	= SCR1_FPU_FMT_F64;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									default	: rvi_illegal = 1'b1;
								endcase // instr[24:20]
							end // 5'b01000

							5'b01011 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FSQRT;
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
							end // 5'b01011

							5'b10100 : begin
								idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
								idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;

								case (funct3)
									3'b000	: idu2exu_cmd_o.fpu_cmd	= SCR1_FPU_CMD_FLE;
									3'b001	: idu2exu_cmd_o.fpu_cmd	= SCR1_FPU_CMD_FLT;
									3'b010	: idu2exu_cmd_o.fpu_cmd	= SCR1_FPU_CMD_FEQ;
									default	: rvi_illegal = 1'b1;
								endcase // funct3
							end // 5'b10100

							5'b11000 : begin
								case (instr[24:20])
									5'b00000 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2I;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I32;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;
									end
									5'b00001 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2UI;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I32;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;
									end
									5'b00010 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2I;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I64;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;
									end
									5'b00011 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_F2UI;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I64;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;
									end
									default	: rvi_illegal = 1'b1;
								endcase // instr[24:20]
							end // 5'b11000

							5'b11010 : begin
								case (instr[24:20])
									5'b00000 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_I2F;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I32;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									5'b00001 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_UI2F;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I32;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									5'b00010 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_I2F;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I64;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									5'b00011 : begin
										idu2exu_cmd_o.fpu_cmd 		= SCR1_FPU_CMD_FCVT_UI2F;
										idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
										idu2exu_cmd_o.fpu_int_fmt	= SCR1_FPU_FMT_I64;
										idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
									end
									default	: rvi_illegal = 1'b1;
								endcase // instr[24:20]
							end // 5'b11010

							5'b11100 : begin
								idu2exu_cmd_o.fpu_src_fmt	= SCR1_FPU_FMT_F32;		// FMV X->W/D

								case (funct3)
									3'b000	: begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMV;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FMV;
									end
									3'b001	: begin
										idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FCLASS;
										idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_FPU;
									end
									default	: rvi_illegal = 1'b1;
								endcase // funct3
							end // 5'b11100

							5'b11110 : begin
								idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMV;
								idu2exu_cmd_o.fpu_src_fmt	= SCR1_FPU_FMT_F64;		// FMV W/D->X
								idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FMV;
							end // 5'b11110

							default : rvi_illegal = 1'b1;
						endcase // funct7
					end // SCR1_OPCODE_OP_FP

					SCR1_OPCODE_FMADD			: begin
						idu2exu_cmd_o.instr_rvf	  	= 1'b1;
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
						idu2exu_use_rs3_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE

						case (funct3)
							3'b000	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RNE;
							3'b001	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RTZ;
							3'b010	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RDN;
							3'b011	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RUP;
							3'b100	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RMM;
							3'b111	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_DYN;
							default	: rvi_illegal = 1'b1;
						endcase // funct3

						case (funct7[1:0])
							2'b00	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F32;
							2'b01	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F64;
							default	: rvi_illegal = 1'b1;
						endcase // funct7[1:0]

						idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMADD;
						idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
						idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
					end // SCR1_OPCODE_FMADD

					SCR1_OPCODE_FMSUB			: begin
						idu2exu_cmd_o.instr_rvf	  	= 1'b1;
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
						idu2exu_use_rs3_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE

						case (funct3)
							3'b000	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RNE;
							3'b001	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RTZ;
							3'b010	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RDN;
							3'b011	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RUP;
							3'b100	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RMM;
							3'b111	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_DYN;
							default	: rvi_illegal = 1'b1;
						endcase // funct3

						case (funct7[1:0])
							2'b00	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F32;
							2'b01	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F64;
							default	: rvi_illegal = 1'b1;
						endcase // funct7[1:0]

						idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FMSUB;
						idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
						idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
					end // SCR1_OPCODE_FMADD

					SCR1_OPCODE_FNMSUB			: begin
						idu2exu_cmd_o.instr_rvf	  	= 1'b1;
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
						idu2exu_use_rs3_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE

						case (funct3)
							3'b000	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RNE;
							3'b001	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RTZ;
							3'b010	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RDN;
							3'b011	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RUP;
							3'b100	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RMM;
							3'b111	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_DYN;
							default	: rvi_illegal = 1'b1;
						endcase // funct3

						case (funct7[1:0])
							2'b00	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F32;
							2'b01	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F64;
							default	: rvi_illegal = 1'b1;
						endcase // funct7[1:0]

						idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FNMSUB;
						idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
						idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
					end // SCR1_OPCODE_FMADD

					SCR1_OPCODE_FNMADD			: begin
						idu2exu_cmd_o.instr_rvf	  	= 1'b1;
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
						idu2exu_use_rs3_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE

						case (funct3)
							3'b000	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RNE;
							3'b001	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RTZ;
							3'b010	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RDN;
							3'b011	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RUP;
							3'b100	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_RMM;
							3'b111	: idu2exu_cmd_o.fpu_rnd = SCR1_FPU_RND_DYN;
							default	: rvi_illegal = 1'b1;
						endcase // funct3

						case (funct7[1:0])
							2'b00	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F32;
							2'b01	: idu2exu_cmd_o.fpu_dst_fmt	= SCR1_FPU_FMT_F64;
							default	: rvi_illegal = 1'b1;
						endcase // funct7[1:0]

						idu2exu_cmd_o.fpu_cmd		= SCR1_FPU_CMD_FNMADD;
						idu2exu_cmd_o.fpu_src_fmt	= idu2exu_cmd_o.fpu_dst_fmt;
						idu2exu_cmd_o.rd_f_wb_sel	= SCR1_RD_F_WB_FPU;
					end // SCR1_OPCODE_FMADD

                    SCR1_OPCODE_OP_IMM          : begin
                        idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:20]};
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                        case (funct3)
                            3'b000  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_ADD;        // ADDI
                            3'b010  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SUB_LT;     // SLTI
                            3'b011  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_SUB_LTU;    // SLTIU
                            3'b100  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_XOR;        // XORI
                            3'b110  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_OR;         // ORI
                            3'b111  : idu2exu_cmd_o.ialu_cmd  = SCR1_IALU_CMD_AND;        // ANDI
                            3'b001  : begin
                                case (funct6)
                                    6'b000000  : begin
                                        // SLLI
                                        idu2exu_cmd_o.imm         = `SCR1_XLEN'(shamt);   // zero-extend
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SLL;
                                    end
                                    default     : rvi_illegal   = 1'b1;
                                endcase // funct6
                            end
                            3'b101  : begin
                                case (funct6)
                                    6'b000000  : begin
                                        // SRLI
                                        idu2exu_cmd_o.imm         = `SCR1_XLEN'(shamt);   // zero-extend
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SRL;
                                    end
                                    6'b010000  : begin
                                        // SRAI
                                        idu2exu_cmd_o.imm         = `SCR1_XLEN'(shamt);   // zero-extend
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SRA;
                                    end
                                    default     : rvi_illegal   = 1'b1;
                                endcase // funct6
                            end
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_OP_IMM

					SCR1_OPCODE_OP_W_IMM		: begin
						idu2exu_use_rs1_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE					
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {21{instr[31]}}, instr[30:20]};
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
						case (funct3)
							3'b000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ADDW;
							3'b001	: begin
								idu2exu_cmd_o.imm		= `SCR1_XLEN'(shamt[4:0]);
								idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SLLW;
							end // 3'b001
							3'b101	: begin
								case (funct7)
									7'b0000000	: begin
										idu2exu_cmd_o.imm		= `SCR1_XLEN'(shamt[4:0]);
										idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SRLW;
									end // 7'b0000000
									7'b0100000	: begin
										idu2exu_cmd_o.imm		= `SCR1_XLEN'(shamt[4:0]);
										idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SRAW;
									end // 7'b0100000
									default : rvi_illegal = 1'b1;
								endcase // funct7
							end // 3'b101
							default	: rvi_illegal = 1'b1;
						endcase // funct3
					end // SCR1_OPCODE_OP_W_IMM

					SCR1_OPCODE_AMO			: begin
						idu2exu_use_rs1_o			= 1'b1;
						idu2exu_use_rs2_o			= 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          	= 1'b1;
						idu2exu_use_imm_o			= 1'b1;
`endif // SCR1_NO_EXE_STAGE
						idu2exu_cmd_o.ialu_op		= SCR1_IALU_OP_AMO_REG;
                        idu2exu_cmd_o.sum2_op     	= SCR1_SUM2_OP_REG_IMM;
						idu2exu_cmd_o.rd_wb_sel		= SCR1_RD_WB_AMO;
						idu2exu_cmd_o.imm			= 64'd0;

						case (funct3)
							3'b010	: begin
								idu2exu_cmd_o.amo_cmd	= SCR1_AMO_CMD_WORD;
								case (funct7[6:2])
									5'b00000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ADDW;
									5'b00001	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SWAPW;
									5'b00010	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_LRW;
									5'b00011	: begin
										idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SCW;
										idu2exu_cmd_o.rd_wb_sel	= SCR1_RD_WB_IALU;
									end
									5'b00100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_XORW;
									5'b01000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ORW;
									5'b01100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ANDW;
									5'b10000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MINW;
									5'b10100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MAXW;
									5'b11000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MINUW;
									5'b11100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MAXUW;
									default		: rvi_illegal = 1'b1;
								endcase // funct7[6:2]
							end // 3'b010

							3'b011	: begin
								idu2exu_cmd_o.amo_cmd	= SCR1_AMO_CMD_DWORD;
								case (funct7[6:2])
									5'b00000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_ADD;
									5'b00001	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SWAP;
									5'b00010	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_LR;
									5'b00011	: begin
										idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_SC;
										idu2exu_cmd_o.rd_wb_sel	= SCR1_RD_WB_IALU;
									end
									5'b00100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_XOR;
									5'b01000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_OR;
									5'b01100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_AND;
									5'b10000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MIN;
									5'b10100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MAX;
									5'b11000	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MINU;
									5'b11100	: idu2exu_cmd_o.ialu_cmd	= SCR1_IALU_CMD_MAXU;
									default		: rvi_illegal = 1'b1;
								endcase // funct7[6:2]
							end // 3'b011
							default : rvi_illegal = 1'b1;
						endcase // funct3
					end // SCR1_OPCODE_AMO

                    SCR1_OPCODE_MISC_MEM    : begin
                        case (funct3)
                            3'b000  : begin
                                if (~|{instr[31:28], instr[19:15], instr[11:7]}) begin
                                    // FENCE = NOP
                                end
                                else rvi_illegal = 1'b1;
                            end
                            3'b001  : begin
                                if (~|{instr[31:15], instr[11:7]}) begin
                                    // FENCE.I
                                    idu2exu_cmd_o.fencei_req    = 1'b1;
                                end
                                else rvi_illegal = 1'b1;
                            end
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
                    end // SCR1_OPCODE_MISC_MEM

                    SCR1_OPCODE_BRANCH          : begin
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.imm         = {{32{instr[31]}}, {20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
                        idu2exu_cmd_o.branch_req  = 1'b1;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                        case (funct3)
                            3'b000  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_EQ;
                            3'b001  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_NE;
                            3'b100  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_LT;
                            3'b101  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_GE;
                            3'b110  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_LTU;
                            3'b111  : idu2exu_cmd_o.ialu_cmd = SCR1_IALU_CMD_SUB_GEU;
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
`ifdef SCR1_RVE_EXT
                        if (instr[19] | instr[24])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_BRANCH

                    SCR1_OPCODE_JALR        : begin
                        idu2exu_use_rs1_o     = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o      = 1'b1;
                        idu2exu_use_imm_o     = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        case (funct3)
                            3'b000  : begin
                                // JALR
                                idu2exu_cmd_o.sum2_op   = SCR1_SUM2_OP_REG_IMM;
                                idu2exu_cmd_o.rd_wb_sel = SCR1_RD_WB_INC_PC;
                                idu2exu_cmd_o.jump_req  = 1'b1;
                                idu2exu_cmd_o.imm       = {{32{instr[31]}}, {21{instr[31]}}, instr[30:20]};
                            end
                            default : rvi_illegal = 1'b1;
                        endcase
`ifdef SCR1_RVE_EXT
                        if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end // SCR1_OPCODE_JALR

                    SCR1_OPCODE_SYSTEM      : begin
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o      = 1'b1;
                        idu2exu_use_imm_o     = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.imm     = `SCR1_XLEN'({funct3, instr[31:20]});      // {funct3, CSR address}
                        case (funct3)
                            3'b000  : begin
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_rd_o    = 1'b0;
                                idu2exu_use_imm_o   = 1'b0;
`endif // SCR1_NO_EXE_STAGE
								case (funct7)
									7'b0000000 : begin
										case (instr[24:20])
											5'b00000 : begin
												// ECALL
                                                idu2exu_cmd_o.exc_req     = 1'b1;
                                                idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_ECALL_M;

												if(|instr[19:7]) rvi_illegal = 1'b1;
											end // 5'b00000
											5'b00001 : begin
												// EBREAK
                                                idu2exu_cmd_o.exc_req     = 1'b1;
                                                idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_BREAKPOINT;

												if(|instr[19:7]) rvi_illegal = 1'b1;
											end // 5'b00001
											default : rvi_illegal = 1'b1;
										endcase // instr[24:20]
									end // 7'b0000000
									7'b0001000 : begin
										case (instr[24:20])
											5'b00010 : begin
												// SRET
												idu2exu_cmd_o.sret_req	  = 1'b1;

												if(|instr[19:7]) rvi_illegal = 1'b1;
											end // 5'b00010
											5'b00101 : begin
												// SRET
												idu2exu_cmd_o.wfi_req	  = 1'b1;

												if(|instr[19:7]) rvi_illegal = 1'b1;
											end // 5'b00101
											default : rvi_illegal = 1'b1;
										endcase // instr[24:20]
									end // 7'b0001000
									7'b0001001 : begin
										// SFENCE.VMA
										idu2exu_cmd_o.sfence_req		= 1'b1;
										idu2exu_use_rs1_o				= 1'b1;
										idu2exu_use_rs2_o				= 1'b1;
									end // 7'b0001001
									7'b0011000 : begin
										case (instr[24:20])
											5'b00010 : begin
												// SRET
												idu2exu_cmd_o.mret_req	  = 1'b1;

												if(|instr[19:7]) rvi_illegal = 1'b1;
											end // 5'b00010
											default : rvi_illegal = 1'b1;
										endcase // inst[24:20]
									end // 7'b0011000
									default : rvi_illegal = 1'b1;
								endcase // funct7
                            end
                            3'b001  : begin
                                // CSRRW
                                idu2exu_use_rs1_o             = 1'b1;
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_WRITE;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_REG;
`ifdef SCR1_RVE_EXT
                                if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            3'b010  : begin
                                // CSRRS
                                idu2exu_use_rs1_o             = 1'b1;
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_SET;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_REG;
`ifdef SCR1_RVE_EXT
                                if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            3'b011  : begin
                                // CSRRC
                                idu2exu_use_rs1_o             = 1'b1;
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_CLEAR;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_REG;
`ifdef SCR1_RVE_EXT
                                if (instr[11] | instr[19])  rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            3'b101  : begin
                                // CSRRWI
                                idu2exu_use_rs1_o             = 1'b1;             // zimm
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_WRITE;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_IMM;
`ifdef SCR1_RVE_EXT
                                if (instr[11])              rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            3'b110  : begin
                                // CSRRSI
                                idu2exu_use_rs1_o             = 1'b1;             // zimm
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_SET;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_IMM;
`ifdef SCR1_RVE_EXT
                                if (instr[11])              rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            3'b111  : begin
                                // CSRRCI
                                idu2exu_use_rs1_o             = 1'b1;             // zimm
                                idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_CSR;
                                idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_CLEAR;
                                idu2exu_cmd_o.csr_op          = SCR1_CSR_OP_IMM;
`ifdef SCR1_RVE_EXT
                                if (instr[11])              rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                            default : rvi_illegal = 1'b1;
                        endcase // funct3
                    end // SCR1_OPCODE_SYSTEM

                    default : begin
                        rvi_illegal = 1'b1;
                    end
                endcase // rvi_opcode
            end // SCR1_INSTR_RVI

`ifdef SCR1_RVC_EXT

            // Quadrant 0
            SCR1_INSTR_RVC0 : begin
                idu2exu_cmd_o.instr_rvc   = 1'b1;
                idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                case (funct3)
                    3'b000  : begin
                        if (~|instr[12:5])      rvc_illegal = 1'b1;
                        // C.ADDI4SPN
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADD;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rd_addr     = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 22'd0, instr[10:7], instr[12:11], instr[5], instr[6], 2'b00};
                    end
					3'b001  : begin
						// C.FLD
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
						idu2exu_cmd_o.sum2_op	  = SCR1_SUM2_OP_REG_IMM;
						idu2exu_cmd_o.lsu_cmd	  = SCR1_LSU_CMD_FLD;
                        idu2exu_cmd_o.rd_f_wb_sel = SCR1_RD_F_WB_LSU;
						idu2exu_cmd_o.rs1_addr	  = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rd_addr     = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[6:5], instr[12:10], 3'b000};
					end
                    3'b010  : begin
                        // C.LW
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_LW;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_LSU;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rd_addr     = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 25'd0, instr[5], instr[12:10], instr[6], 2'b00};
                    end
					3'b011	: begin
						// C.LD
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
						idu2exu_cmd_o.sum2_op	  = SCR1_SUM2_OP_REG_IMM;
						idu2exu_cmd_o.lsu_cmd	  = SCR1_LSU_CMD_LD;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_LSU;
						idu2exu_cmd_o.rs1_addr	  = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rd_addr     = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[6:5], instr[12:10], 3'b000};
					end
					3'b101  : begin
                        // C.FSD
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_FSD;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[6:5], instr[12:10], 3'b000};
					end
                    3'b110  : begin
                        // C.SW
                        idu2exu_use_rs2_o         = 1'b1;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_SW;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 25'd0, instr[5], instr[12:10], instr[6], 2'b00};
                    end
                    3'b111  : begin
                        // C.SD
                        idu2exu_use_rs2_o         = 1'b1;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_SD;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = {2'b01, instr[4:2]};
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[6:5], instr[12:10], 3'b000};
                    end
                    default : begin
                        rvc_illegal = 1'b1;
                    end
                endcase // funct3
            end // Quadrant 0

            // Quadrant 1
            SCR1_INSTR_RVC1 : begin
                idu2exu_cmd_o.instr_rvc   = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                idu2exu_use_rd_o          = 1'b1;
                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                case (funct3)
                    3'b000  : begin
                        // C.ADDI / C.NOP
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADD;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                        idu2exu_cmd_o.rs1_addr    = instr[11:7];
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {27{instr[12]}}, instr[6:2]};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end
                    3'b001  : begin
                        // C.ADDIW
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADDW;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                        idu2exu_cmd_o.rs1_addr    = instr[11:7];
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {27{instr[12]}}, instr[6:2]};
                    end
                    3'b010  : begin
                        // C.LI
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IMM;
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {27{instr[12]}}, instr[6:2]};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end
                    3'b011  : begin
                        if (~|{instr[12], instr[6:2]}) rvc_illegal = 1'b1;
                        if (instr[11:7] == SCR1_MPRF_SP_ADDR) begin
                            // C.ADDI16SP
                            idu2exu_use_rs1_o         = 1'b1;
                            idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADD;
                            idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                            idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                            idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                            idu2exu_cmd_o.rd_addr     = SCR1_MPRF_SP_ADDR;
                            idu2exu_cmd_o.imm         = {{32{instr[12]}}, {23{instr[12]}}, instr[4:3], instr[5], instr[2], instr[6], 4'd0};
                        end else begin
                            // C.LUI
                            idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IMM;
                            idu2exu_cmd_o.rd_addr     = instr[11:7];
                            idu2exu_cmd_o.imm         = {{32{instr[12]}}, {15{instr[12]}}, instr[6:2], 12'd0};
`ifdef SCR1_RVE_EXT
                            if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                        end
                    end
                    3'b100  : begin
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rd_addr     = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = {2'b01, instr[4:2]};
                        idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        case (instr[11:10])
                            2'b00   : begin
                                // C.SRLI
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SRL;
                                idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                
								case (|{instr[12],instr[6:2]})
									1'b0 : idu2exu_cmd_o.imm         = {32'd0, 25'd0, 7'b100_0000};
									1'b1 : idu2exu_cmd_o.imm         = {32'd0, 26'd0, instr[12], instr[6:2]};
								endcase
                            end
                            2'b01   : begin
                                // C.SRAI
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.imm         = {32'd0, 27'd0, instr[6:2]};
                                idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SRA;
                                idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;

								case (|{instr[12],instr[6:2]})
									1'b0 : idu2exu_cmd_o.imm         = {32'd0, 25'd0, 7'b100_0000};
									1'b1 : idu2exu_cmd_o.imm         = {32'd0, 26'd0, instr[12], instr[6:2]};
								endcase

                            end
                            2'b10   : begin
                                // C.ANDI
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_AND;
                                idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                idu2exu_cmd_o.imm         = {{32{instr[12]}}, {27{instr[12]}}, instr[6:2]};
                            end
                            2'b11   : begin
                                idu2exu_use_rs2_o         = 1'b1;
                                case ({instr[12], instr[6:5]})
                                    3'b000  : begin
                                        // C.SUB
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SUB;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                    end
                                    3'b001  : begin
                                        // C.XOR
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_XOR;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                    end
                                    3'b010  : begin
                                        // C.OR
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_OR;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                    end
                                    3'b011  : begin
                                        // C.AND
                                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_AND;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                    end
									3'b100  : begin
										// C.SUBW
										idu2exu_cmd_o.ialu_cmd	  = SCR1_IALU_CMD_SUBW;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
									end
									3'b101  : begin
										// C.ADDW
										idu2exu_cmd_o.ialu_cmd	  = SCR1_IALU_CMD_ADDW;
                                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
									end
                                    default : begin
                                        rvc_illegal = 1'b1;
                                    end
                                endcase // {instr[12], instr[6:5]}
                            end
                        endcase // instr[11:10]
                    end // funct3 == 3'b100
                    3'b101  : begin
                        // C.J
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.jump_req    = 1'b1;
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {21{instr[12]}}, instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], 1'b0};
                    end
                    3'b110  : begin
                        // C.BEQZ
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SUB_EQ;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.branch_req  = 1'b1;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = SCR1_MPRF_ZERO_ADDR;
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {24{instr[12]}}, instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0};
                    end
                    3'b111  : begin
                        // C.BNEZ
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SUB_NE;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_PC_IMM;
                        idu2exu_cmd_o.branch_req  = 1'b1;
                        idu2exu_cmd_o.rs1_addr    = {2'b01, instr[9:7]};
                        idu2exu_cmd_o.rs2_addr    = SCR1_MPRF_ZERO_ADDR;
                        idu2exu_cmd_o.imm         = {{32{instr[12]}}, {24{instr[12]}}, instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0};
                    end
                endcase // funct3
            end // Quadrant 1

            // Quadrant 2
            SCR1_INSTR_RVC2 : begin
                idu2exu_cmd_o.instr_rvc   = 1'b1;
                idu2exu_use_rs1_o         = 1'b1;
                case (funct3)
                    3'b000  : begin
                        // C.SLLI
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.rs1_addr    = instr[11:7];
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_SLL;
                        idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_IMM;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;

						case (|{instr[12],instr[6:2]})
							1'b0 : idu2exu_cmd_o.imm         = {32'd0, 25'd0, 7'b100_0000};
							1'b1 : idu2exu_cmd_o.imm         = {32'd0, 26'd0, instr[12], instr[6:2]};
						endcase
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end
					3'b001  : begin
						// C.FLDSP
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_FLD;
                        idu2exu_cmd_o.rd_f_wb_sel = SCR1_RD_F_WB_LSU;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {32'd0, 23'd0, instr[4:2], instr[12], instr[6:5], 3'b000};
					end
                    3'b010  : begin
                        if (~|instr[11:7])      rvc_illegal = 1'b1;
                        // C.LWSP
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_LW;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_LSU;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[3:2], instr[12], instr[6:4], 2'b00};
`ifdef SCR1_RVE_EXT
                        if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end
                    3'b011  : begin
                        if (~|instr[11:7])      rvc_illegal = 1'b1;
                        // C.LDSP
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_rd_o          = 1'b1;
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_LD;
                        idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_LSU;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rd_addr     = instr[11:7];
                        idu2exu_cmd_o.imm         = {32'd0, 23'd0, instr[4:2], instr[12], instr[6:5], 3'b000};
                    end
                    3'b100  : begin
                        if (~instr[12]) begin
                            if (|instr[6:2]) begin
                                // C.MV
                                idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADD;
                                idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_ZERO_ADDR;
                                idu2exu_cmd_o.rs2_addr    = instr[6:2];
                                idu2exu_cmd_o.rd_addr     = instr[11:7];
`ifdef SCR1_RVE_EXT
                                if (instr[11]|instr[6]) rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end else begin
                                if (~|instr[11:7])      rvc_illegal = 1'b1;
                                // C.JR
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                                idu2exu_cmd_o.jump_req    = 1'b1;
                                idu2exu_cmd_o.rs1_addr    = instr[11:7];
                                idu2exu_cmd_o.imm         = 0;
`ifdef SCR1_RVE_EXT
                                if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                        end else begin  // instr[12] == 1
                            if (~|instr[11:2]) begin
                                // C.EBREAK
                                idu2exu_cmd_o.exc_req     = 1'b1;
                                idu2exu_cmd_o.exc_code    = SCR1_EXC_CODE_BREAKPOINT;
                            end else if (~|instr[6:2]) begin
                                // C.JALR
                                idu2exu_use_rs1_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_rd_o          = 1'b1;
                                idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_INC_PC;
                                idu2exu_cmd_o.jump_req    = 1'b1;
                                idu2exu_cmd_o.rs1_addr    = instr[11:7];
                                idu2exu_cmd_o.rd_addr     = SCR1_MPRF_RA_ADDR;
                                idu2exu_cmd_o.imm         = 0;
`ifdef SCR1_RVE_EXT
                                if (instr[11])          rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end else begin
                                // C.ADD
                                idu2exu_use_rs1_o         = 1'b1;
                                idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                                idu2exu_use_rd_o          = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                                idu2exu_cmd_o.ialu_cmd    = SCR1_IALU_CMD_ADD;
                                idu2exu_cmd_o.ialu_op     = SCR1_IALU_OP_REG_REG;
                                idu2exu_cmd_o.rd_wb_sel   = SCR1_RD_WB_IALU;
                                idu2exu_cmd_o.rs1_addr    = instr[11:7];
                                idu2exu_cmd_o.rs2_addr    = instr[6:2];
                                idu2exu_cmd_o.rd_addr     = instr[11:7];
`ifdef SCR1_RVE_EXT
                                if (instr[11]|instr[6]) rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                            end
                        end // instr[12] == 1
                    end
                    3'b101  : begin
                        // C.FSDSP
						idu2exu_cmd_o.instr_rvf	  = 1'b1;
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_FSD;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rs2_addr    = instr[6:2];
                        idu2exu_cmd_o.imm         = {32'd0, 23'd0, instr[9:7], instr[12:10], 3'b000};
                    end
                    3'b110  : begin
                        // C.SWSP
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_SW;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rs2_addr    = instr[6:2];
                        idu2exu_cmd_o.imm         = {32'd0, 24'd0, instr[8:7], instr[12:9], 2'b00};
`ifdef SCR1_RVE_EXT
                        if (instr[6])           rve_illegal = 1'b1;
`endif  // SCR1_RVE_EXT
                    end
                    3'b111  : begin
                        // C.SDSP
                        idu2exu_use_rs1_o         = 1'b1;
                        idu2exu_use_rs2_o         = 1'b1;
`ifndef SCR1_NO_EXE_STAGE
                        idu2exu_use_imm_o         = 1'b1;
`endif // SCR1_NO_EXE_STAGE
                        idu2exu_cmd_o.sum2_op     = SCR1_SUM2_OP_REG_IMM;
                        idu2exu_cmd_o.lsu_cmd     = SCR1_LSU_CMD_SD;
                        idu2exu_cmd_o.rs1_addr    = SCR1_MPRF_SP_ADDR;
                        idu2exu_cmd_o.rs2_addr    = instr[6:2];
                        idu2exu_cmd_o.imm         = {32'd0, 23'd0, instr[9:7], instr[12:10], 3'b000};
                    end
                    default : begin
                        rvc_illegal = 1'b1;
                    end
                endcase // funct3
            end // Quadrant 2

            default         : begin
`ifdef SCR1_XPROP_EN
                rvi_illegal             = 1'b1;
`endif // SCR1_XPROP_EN
            end
`else   // SCR1_RVC_EXT
            default         : begin
                idu2exu_cmd_o.instr_rvc = 1'b1;
                rvi_illegal             = 1'b1;
            end
`endif  // SCR1_RVC_EXT
        endcase // instr_type
    end // no imem fault

    // At this point the instruction is fully decoded
    // given that no imem fault has happened

    // Check illegal instruction
    if (
    rvi_illegal
`ifdef SCR1_RVC_EXT
    | rvc_illegal
`endif
`ifdef SCR1_RVE_EXT
    | rve_illegal
`endif
    ) begin
        idu2exu_cmd_o.ialu_cmd        = SCR1_IALU_CMD_NONE;
        idu2exu_cmd_o.lsu_cmd         = SCR1_LSU_CMD_NONE;
        idu2exu_cmd_o.csr_cmd         = SCR1_CSR_CMD_NONE;
        idu2exu_cmd_o.rd_wb_sel       = SCR1_RD_WB_NONE;
        idu2exu_cmd_o.jump_req        = 1'b0;
        idu2exu_cmd_o.branch_req      = 1'b0;
        idu2exu_cmd_o.mret_req        = 1'b0;
        idu2exu_cmd_o.fencei_req      = 1'b0;
        idu2exu_cmd_o.wfi_req         = 1'b0;
		idu2exu_cmd_o.sfence_req	  = 1'b0;

        idu2exu_use_rs1_o             = 1'b0;
        idu2exu_use_rs2_o             = 1'b0;
`ifndef SCR1_NO_EXE_STAGE
        idu2exu_use_rd_o              = 1'b0;
`endif // SCR1_NO_EXE_STAGE

`ifndef SCR1_MTVAL_ILLEGAL_INSTR_EN
        idu2exu_use_imm_o             = 1'b0;
`else // SCR1_MTVAL_ILLEGAL_INSTR_EN
`ifndef SCR1_NO_EXE_STAGE
        idu2exu_use_imm_o             = 1'b1;
`endif // SCR1_NO_EXE_STAGE
        idu2exu_cmd_o.imm             = instr;
`endif // SCR1_MTVAL_ILLEGAL_INSTR_EN

        idu2exu_cmd_o.exc_req         = 1'b1;
        idu2exu_cmd_o.exc_code        = SCR1_EXC_CODE_ILLEGAL_INSTR;
    end

end // RV32I(MC) decode

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_IDU_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({ifu2idu_vd_i, exu2idu_rdy_i})
    ) else $error("IDU Error: unknown values");

// Behavior checks

SCR1_SVA_IDU_IALU_CMD_RANGE : assert property (
    @(negedge clk) disable iff (~rst_n)
    (ifu2idu_vd_i & ~ifu2idu_imem_err_i) |->
    ((idu2exu_cmd_o.ialu_cmd >= SCR1_IALU_CMD_NONE) &
    (idu2exu_cmd_o.ialu_cmd <=
`ifdef SCR1_RVM_EXT
                            SCR1_IALU_CMD_REMUW
`else
                            SCR1_IALU_CMD_MAXUW
`endif // SCR1_RVM_EXT
        ))
    ) else $error("IDU Error: IALU_CMD out of range");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_idu
