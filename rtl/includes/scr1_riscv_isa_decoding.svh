/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_riscv_isa_decoding.svh>
/// @brief      RISC-V ISA definitions file
///

`ifndef SCR1_RISCV_ISA_DECODING_SVH
`define SCR1_RISCV_ISA_DECODING_SVH

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"

//-------------------------------------------------------------------------------
// Instruction types
//-------------------------------------------------------------------------------
typedef enum logic [1:0] {
    SCR1_INSTR_RVC0     = 2'b00,
    SCR1_INSTR_RVC1     = 2'b01,
    SCR1_INSTR_RVC2     = 2'b10,
    SCR1_INSTR_RVI      = 2'b11
} type_scr1_instr_type_e;

//-------------------------------------------------------------------------------
// RV32I opcodes (bits 6:2)
//-------------------------------------------------------------------------------
typedef enum logic [6:2] {
    SCR1_OPCODE_LOAD        = 5'b00000,
	SCR1_OPCODE_LOAD_FP		= 5'b00001,
    SCR1_OPCODE_MISC_MEM    = 5'b00011,
    SCR1_OPCODE_OP_IMM      = 5'b00100,
    SCR1_OPCODE_OP_W_IMM    = 5'b00110,
    SCR1_OPCODE_AUIPC       = 5'b00101,
    SCR1_OPCODE_STORE       = 5'b01000,
	SCR1_OPCODE_STORE_FP	= 5'b01001,
	SCR1_OPCODE_AMO			= 5'b01011,
    SCR1_OPCODE_OP          = 5'b01100,
    SCR1_OPCODE_OP_W        = 5'b01110,
    SCR1_OPCODE_LUI         = 5'b01101,
	SCR1_OPCODE_FMADD		= 5'b10000,
	SCR1_OPCODE_FMSUB		= 5'b10001,
	SCR1_OPCODE_FNMSUB		= 5'b10010,
	SCR1_OPCODE_FNMADD		= 5'b10011,
	SCR1_OPCODE_OP_FP		= 5'b10100,
    SCR1_OPCODE_BRANCH      = 5'b11000,
    SCR1_OPCODE_JALR        = 5'b11001,
    SCR1_OPCODE_JAL         = 5'b11011,
    SCR1_OPCODE_SYSTEM      = 5'b11100
} type_scr1_rvi_opcode_e;


//-------------------------------------------------------------------------------
// IALU main operands
//-------------------------------------------------------------------------------
localparam SCR1_IALU_OP_ALL_NUM_E = 3;
localparam SCR1_IALU_OP_WIDTH_E   = $clog2(SCR1_IALU_OP_ALL_NUM_E);
typedef enum logic [SCR1_IALU_OP_WIDTH_E-1:0] {
    SCR1_IALU_OP_REG_IMM,          // op1 = rs1; op2 = imm
    SCR1_IALU_OP_REG_REG,          // op1 = rs1; op2 = rs2
	SCR1_IALU_OP_AMO_REG		   // op1 = atomical loaded value; op2 = rs2
} type_scr1_ialu_op_sel_e;

//-------------------------------------------------------------------------------
// IALU main commands
//-------------------------------------------------------------------------------
`ifdef SCR1_RVM_EXT
localparam SCR1_IALU_CMD_ALL_NUM_E    = 37 + 13;
`else // ~SCR1_RVM_EXT
localparam SCR1_IALU_CMD_ALL_NUM_E    = 37;
`endif // ~SCR1_RVM_EXT
localparam SCR1_IALU_CMD_WIDTH_E      = $clog2(SCR1_IALU_CMD_ALL_NUM_E);
typedef enum logic [SCR1_IALU_CMD_WIDTH_E-1:0] {
    SCR1_IALU_CMD_NONE  = '0,   // IALU disable
    SCR1_IALU_CMD_AND,          // op1 & op2
    SCR1_IALU_CMD_OR,           // op1 | op2
    SCR1_IALU_CMD_XOR,          // op1 ^ op2
    SCR1_IALU_CMD_ADD,          // op1 + op2
    SCR1_IALU_CMD_SUB,          // op1 - op2
    SCR1_IALU_CMD_SUB_LT,       // op1 < op2
    SCR1_IALU_CMD_SUB_LTU,      // op1 u< op2
    SCR1_IALU_CMD_SUB_EQ,       // op1 = op2
    SCR1_IALU_CMD_SUB_NE,       // op1 != op2
    SCR1_IALU_CMD_SUB_GE,       // op1 >= op2
    SCR1_IALU_CMD_SUB_GEU,      // op1 u>= op2
    SCR1_IALU_CMD_SLL,          // op1 << op2
    SCR1_IALU_CMD_SRL,          // op1 >> op2
    SCR1_IALU_CMD_SRA,          // op1 >>> op2
	SCR1_IALU_CMD_ADDW,			// ADD w/ low 32b and sign-extend
	SCR1_IALU_CMD_SUBW,			// SUB w/ low 32b and sign-extend
	SCR1_IALU_CMD_SLLW,			// SLL w/ low 32b and sign-extend
	SCR1_IALU_CMD_SRLW,			// SRL w/ low 32b and sign-extend
	SCR1_IALU_CMD_SRAW,			// SRA w/ low 32b and sign-extend
	SCR1_IALU_CMD_LR,			// load reserved
	SCR1_IALU_CMD_SC,			// store conditional
	SCR1_IALU_CMD_LRW,			// load reserved w/ low 32b
	SCR1_IALU_CMD_SCW,			// store conditional w/ low 32b
	SCR1_IALU_CMD_SWAP,			// swap values
	SCR1_IALU_CMD_MIN,			// min(op1, op2)
	SCR1_IALU_CMD_MAX,			// max(op1, op2)
	SCR1_IALU_CMD_MINU,			// min(unsigned(op1), unsigned(op2))
	SCR1_IALU_CMD_MAXU,			// max(unsigned(op1), unsigned(op2))
	SCR1_IALU_CMD_SWAPW,		// swap values w/ low 32b and sign-extend
	SCR1_IALU_CMD_XORW,			// op1 ^ op2 w/ low 32b and sign-extend
	SCR1_IALU_CMD_ORW,			// op1 | op2 w/ low 32b and sign-extend
	SCR1_IALU_CMD_ANDW,			// op1 & op2 w/ low 32b and sign-extend
	SCR1_IALU_CMD_MINW,			// min(op1, op2) w/ low 32b and sign-extend
	SCR1_IALU_CMD_MAXW,			// max(op1, op2) w/ low 32b and sign-extend
	SCR1_IALU_CMD_MINUW,		// min(unsigned(op1), unsigned(op2)) w/ low 32b and sign-extend
	SCR1_IALU_CMD_MAXUW			// max(unsigned(op1), unsigned(op2)) w/ low 32b and sign-extend
`ifdef SCR1_RVM_EXT
    ,
    SCR1_IALU_CMD_MUL,          // low(unsig(op1) * unsig(op2))
    SCR1_IALU_CMD_MULHU,        // high(unsig(op1) * unsig(op2))
    SCR1_IALU_CMD_MULHSU,       // high(op1 * unsig(op2))
    SCR1_IALU_CMD_MULH,         // high(op1 * op2)
    SCR1_IALU_CMD_DIV,          // op1 / op2
    SCR1_IALU_CMD_DIVU,         // op1 u/ op2
    SCR1_IALU_CMD_REM,          // op1 % op2
    SCR1_IALU_CMD_REMU,         // op1 u% op2
	SCR1_IALU_CMD_MULW,			// MUL w/ low 32b and sign-extend
	SCR1_IALU_CMD_DIVW,			// DIV w/ low 32b and sign-extend
	SCR1_IALU_CMD_DIVUW,		// DIVU w/ low 32b and sign-extend
	SCR1_IALU_CMD_REMW,			// REM w/ low 32b and sign-extend
	SCR1_IALU_CMD_REMUW			// REMU w/ low 32b and sign-extend
`endif  // SCR1_RVM_EXT
} type_scr1_ialu_cmd_sel_e;

//-------------------------------------------------------------------------------
// IALU SUM2 operands (result is JUMP/BRANCH target, LOAD/STORE address)
//-------------------------------------------------------------------------------
localparam SCR1_SUM2_OP_ALL_NUM_E    = 2;
localparam SCR1_SUM2_OP_WIDTH_E      = $clog2(SCR1_SUM2_OP_ALL_NUM_E);
typedef enum logic [SCR1_SUM2_OP_WIDTH_E-1:0] {
    SCR1_SUM2_OP_PC_IMM,        // op1 = curr_pc; op2 = imm (AUIPC, target new_pc for JAL and branches)
    SCR1_SUM2_OP_REG_IMM        // op1 = rs1; op2 = imm (target new_pc for JALR, LOAD/STORE address)
`ifdef SCR1_XPROP_EN
    ,
    SCR1_SUM2_OP_ERROR = 'x
`endif // SCR1_XPROP_EN
} type_scr1_ialu_sum2_op_sel_e;

//-------------------------------------------------------------------------------
// LSU commands
//-------------------------------------------------------------------------------
localparam SCR1_LSU_CMD_ALL_NUM_E   = 16;
localparam SCR1_LSU_CMD_WIDTH_E     = $clog2(SCR1_LSU_CMD_ALL_NUM_E);
typedef enum logic [SCR1_LSU_CMD_WIDTH_E-1:0] {
    SCR1_LSU_CMD_NONE = '0,
    SCR1_LSU_CMD_LB,
    SCR1_LSU_CMD_LH,
    SCR1_LSU_CMD_LW,
    SCR1_LSU_CMD_LD,
    SCR1_LSU_CMD_LBU,
    SCR1_LSU_CMD_LHU,
    SCR1_LSU_CMD_LWU,
    SCR1_LSU_CMD_SB,
    SCR1_LSU_CMD_SH,
    SCR1_LSU_CMD_SW,
    SCR1_LSU_CMD_SD,
	SCR1_LSU_CMD_FLW,
	SCR1_LSU_CMD_FLD,
	SCR1_LSU_CMD_FSW,
	SCR1_LSU_CMD_FSD
} type_scr1_lsu_cmd_sel_e;

//-------------------------------------------------------------------------------
// FPU main commands
//-------------------------------------------------------------------------------
localparam SCR1_FPU_CMD_ALL_NUM_E	= 23;
localparam SCR1_FPU_CMD_WIDTH_E		= $clog2(SCR1_FPU_CMD_ALL_NUM_E);
typedef enum logic [SCR1_FPU_CMD_WIDTH_E-1:0] {
    SCR1_FPU_CMD_NONE  = '0,	// FPU disable
    SCR1_FPU_CMD_FMADD,			// op1 * op2 + op3
    SCR1_FPU_CMD_FMSUB,			// op1 * op2 - op3
    SCR1_FPU_CMD_FNMSUB,		// -(op1 * op2) + op3
    SCR1_FPU_CMD_FNMADD,		// -(op1 * op2) - op3
    SCR1_FPU_CMD_FADD,			// op1 + op2
    SCR1_FPU_CMD_FSUB,			// op1 - op2
    SCR1_FPU_CMD_FMUL,			// op1 * op2
    SCR1_FPU_CMD_FDIV,			// op1 / op2
    SCR1_FPU_CMD_FSQRT,			// sqrt(op1)
    SCR1_FPU_CMD_FSGNJ,			// {sign(op2), abs(op1)}
	SCR1_FPU_CMD_FSGNJN,		// {-sign(op2), abs(op1)}
	SCR1_FPU_CMD_FSGNJX,		// {sign(op1)^sign(op2), abs(op1)}
    SCR1_FPU_CMD_FMIN,			// min(op1, op2)
    SCR1_FPU_CMD_FMAX,			// max(op1, op2)
    SCR1_FPU_CMD_FCVT_F2F,		// FP -> FP conversion
    SCR1_FPU_CMD_FCVT_F2I,		// FP -> INT conversion
    SCR1_FPU_CMD_FCVT_F2UI,		// FP -> unsigned INT conversion
    SCR1_FPU_CMD_FCVT_I2F,		// INT -> FP conversion
    SCR1_FPU_CMD_FCVT_UI2F,		// Unsigned INT -> FP conversion
    SCR1_FPU_CMD_FMV,			// move bit pattern without conversion
    SCR1_FPU_CMD_FEQ,			// (op1 == op2)
    SCR1_FPU_CMD_FLT,			// (op1 < op2)
    SCR1_FPU_CMD_FLE,			// (op1 <= op2)
    SCR1_FPU_CMD_FCLASS			// classification of float number
} type_scr1_fpu_cmd_sel_e;

//-------------------------------------------------------------------------------
// FPU rounding formats
//-------------------------------------------------------------------------------
localparam SCR1_FPU_RND_ALL_NUM_E	= 6;
localparam SCR1_FPU_RND_WIDTH_E		= $clog2(SCR1_FPU_RND_ALL_NUM_E);
typedef enum logic [SCR1_FPU_RND_WIDTH_E-1:0] {
    SCR1_FPU_RND_RNE = 3'b000,	// Round to nearest, tie to even
    SCR1_FPU_RND_RTZ = 3'b001,	// Round towards zero
    SCR1_FPU_RND_RDN = 3'b010,	// Round towards -inf
    SCR1_FPU_RND_RUP = 3'b011,	// Round towards +inf
    SCR1_FPU_RND_RMM = 3'b100,	// Round to nearest, ties to MAX
    SCR1_FPU_RND_DYN = 3'b111	// Dynamic rounding
} type_scr1_fpu_rnd_sel_e;

//-------------------------------------------------------------------------------
// FPU data formats
//-------------------------------------------------------------------------------
localparam SCR1_FPU_FMT_ALL_NUM_E	= 4;
localparam SCR1_FPU_FMT_WIDTH_E		= $clog2(SCR1_FPU_FMT_ALL_NUM_E);
typedef enum logic [SCR1_FPU_FMT_WIDTH_E-1:0] {
    SCR1_FPU_FMT_F32  = '0,	// 32-bit FP
    SCR1_FPU_FMT_F64,		// 64-bit FP
    SCR1_FPU_FMT_I32,		// 32-bit INT
    SCR1_FPU_FMT_I64		// 64-bit INT
} type_scr1_fpu_fmt_sel_e;

//-------------------------------------------------------------------------------
// AMO commands
//-------------------------------------------------------------------------------
localparam SCR1_AMO_CMD_ALL_NUM_E	= 3;
localparam SCR1_AMO_CMD_WIDTH_E		= $clog2(SCR1_AMO_CMD_ALL_NUM_E);
typedef enum logic [SCR1_AMO_CMD_WIDTH_E-1:0] {
	SCR1_AMO_CMD_NONE = '0,
	SCR1_AMO_CMD_WORD,
	SCR1_AMO_CMD_DWORD
} type_scr1_amo_cmd_sel_e;

//-------------------------------------------------------------------------------
// CSR operands
//-------------------------------------------------------------------------------
localparam SCR1_CSR_OP_ALL_NUM_E   = 2;
localparam SCR1_CSR_OP_WIDTH_E     = $clog2(SCR1_CSR_OP_ALL_NUM_E);
typedef enum logic [SCR1_CSR_OP_WIDTH_E-1:0] {
    SCR1_CSR_OP_IMM,
    SCR1_CSR_OP_REG
} type_scr1_csr_op_sel_e;

//-------------------------------------------------------------------------------
// CSR commands
//-------------------------------------------------------------------------------
localparam SCR1_CSR_CMD_ALL_NUM_E   = 4;
localparam SCR1_CSR_CMD_WIDTH_E     = $clog2(SCR1_CSR_CMD_ALL_NUM_E);
typedef enum logic [SCR1_CSR_CMD_WIDTH_E-1:0] {
    SCR1_CSR_CMD_NONE = '0,
    SCR1_CSR_CMD_WRITE,
    SCR1_CSR_CMD_SET,
    SCR1_CSR_CMD_CLEAR
} type_scr1_csr_cmd_sel_e;

//-------------------------------------------------------------------------------
// MPRF rd writeback source
//-------------------------------------------------------------------------------
localparam SCR1_RD_WB_ALL_NUM_E = 9;
localparam SCR1_RD_WB_WIDTH_E   = $clog2(SCR1_RD_WB_ALL_NUM_E);
typedef enum logic [SCR1_RD_WB_WIDTH_E-1:0] {
    SCR1_RD_WB_NONE = '0,
    SCR1_RD_WB_IALU,            // IALU main result
    SCR1_RD_WB_SUM2,            // IALU SUM2 result (AUIPC)
    SCR1_RD_WB_IMM,             // LUI
    SCR1_RD_WB_INC_PC,          // JAL(R)
    SCR1_RD_WB_LSU,             // Load from DMEM
	SCR1_RD_WB_FPU,				// FCVT, FP CMP, FCLASS
	SCR1_RD_WB_FMV,				// FMV from fp to int
	SCR1_RD_WB_AMO,				// atomically loaded data
    SCR1_RD_WB_CSR              // Read CSR
} type_scr1_rd_wb_sel_e;

//-------------------------------------------------------------------------------
// F-MPRF rd writeback source
//-------------------------------------------------------------------------------
localparam SCR1_RD_F_WB_ALL_NUM_E = 5;
localparam SCR1_RD_F_WB_WIDTH_E   = $clog2(SCR1_RD_F_WB_ALL_NUM_E);
typedef enum logic [SCR1_RD_F_WB_WIDTH_E-1:0] {
    SCR1_RD_F_WB_NONE = '0,
    SCR1_RD_F_WB_FPU,           // FPU main result
    SCR1_RD_F_WB_LSU,           // Load from DMEM
    SCR1_RD_F_WB_FMV,           // FMV from int to fp 
    SCR1_RD_F_WB_CSR            // Read CSR
} type_scr1_rd_f_wb_sel_e;

//-------------------------------------------------------------------------------
// IDU to EXU full command structure
//-------------------------------------------------------------------------------
localparam SCR1_GPR_FIELD_WIDTH = 5;

typedef struct packed {
    logic                               instr_rvc;      // used with a different meaning for IFU access fault exception
	logic								instr_rvf;
    type_scr1_ialu_op_sel_e             ialu_op;
    type_scr1_ialu_cmd_sel_e            ialu_cmd;
    type_scr1_ialu_sum2_op_sel_e        sum2_op;
    type_scr1_lsu_cmd_sel_e             lsu_cmd;
	type_scr1_fpu_cmd_sel_e				fpu_cmd;
	type_scr1_fpu_rnd_sel_e				fpu_rnd;
	type_scr1_fpu_fmt_sel_e				fpu_src_fmt;
	type_scr1_fpu_fmt_sel_e				fpu_dst_fmt;
	type_scr1_fpu_fmt_sel_e				fpu_int_fmt;
	type_scr1_amo_cmd_sel_e				amo_cmd;
    type_scr1_csr_op_sel_e              csr_op;
    type_scr1_csr_cmd_sel_e             csr_cmd;
    type_scr1_rd_wb_sel_e               rd_wb_sel;
    type_scr1_rd_f_wb_sel_e             rd_f_wb_sel;
    logic                               jump_req;
    logic                               branch_req;
    logic                               mret_req;
    logic                               sret_req;
    logic                               fencei_req;
    logic                               wfi_req;
	logic								sfence_req;
    logic [SCR1_GPR_FIELD_WIDTH-1:0]    rs1_addr;       // also used as zimm for CSRRxI instructions
    logic [SCR1_GPR_FIELD_WIDTH-1:0]    rs2_addr;
    logic [SCR1_GPR_FIELD_WIDTH-1:0]    rs3_addr;
    logic [SCR1_GPR_FIELD_WIDTH-1:0]    rd_addr;
    logic [`SCR1_XLEN-1:0]              imm;            // used as {funct3, CSR address} for CSR instructions
                                                        // used as instruction field for illegal instruction exception
    logic                               exc_req;
    type_scr1_exc_code_e                exc_code;
} type_scr1_exu_cmd_s;



`endif // SCR1_RISCV_ISA_DECODING_SVH

