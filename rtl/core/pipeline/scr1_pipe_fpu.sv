/// Copyright by ETRI LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_pipe_fprf.sv>
/// @brief      Floating-Point Register File (FPRF)
///
//
`include "scr1_riscv_isa_decoding.svh"

import fpnew_pkg::*;

module scr1_pipe_fpu 
(
    input	logic						clk,
    input	logic						rst_n,

    input	logic [`SCR1_XLEN-1:0]		exu2fpu_main_op1_i,
    input	logic [`SCR1_XLEN-1:0]		exu2fpu_main_op2_i,
    input	logic [`SCR1_XLEN-1:0]		exu2fpu_main_op3_i,
    input	logic [`SCR1_XLEN-1:0]		exu2fpu_int_op_i,

    input	type_scr1_fpu_cmd_sel_e		exu2fpu_cmd_i,
    input	type_scr1_fpu_rnd_sel_e		exu2fpu_rnd_i,
	input	logic [2:0]					exu2fpu_frm_i,

    input	type_scr1_fpu_fmt_sel_e		exu2fpu_src_fmt_i,
    input	type_scr1_fpu_fmt_sel_e		exu2fpu_dst_fmt_i,
    input	type_scr1_fpu_fmt_sel_e		exu2fpu_int_fmt_i,

    input	logic						exu2fpu_valid_i,
    output	logic						fpu2exu_ready_o,
    output	logic [`SCR1_XLEN-1:0]		fpu2exu_result_o,
	output	logic [4:0]					fpu2exu_status_o
);

// FSM
typedef enum logic {
    FSM_FPU_IDLE	= 1'b0,
    FSM_FPU_RUN		= 1'b1
} fsm_fpu_e;

// FPU implementation type
localparam fpnew_pkg::fpu_implementation_t FPU_IMP_REGS_1 = '{
  PipeRegs:   '{default: 1},
  UnitTypes:  '{'{default: fpnew_pkg::PARALLEL}, // ADDMUL
                '{default: fpnew_pkg::MERGED},   // DIVSQRT
                '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                '{default: fpnew_pkg::MERGED}},  // CONV
  PipeConfig: fpnew_pkg::BEFORE
};

//----------------------------------------------
// FPU control signals
//----------------------------------------------

// FPnew
logic [2:0][`SCR1_XLEN-1:0] 	fpnew_operands;
fpnew_pkg::roundmode_e			fpnew_rnd_mode;
fpnew_pkg::roundmode_e			fpnew_rnd_normal;
fpnew_pkg::roundmode_e			fpnew_dynamic_rnd;
fpnew_pkg::roundmode_e			fpnew_rnd_for_cmd;

fpnew_pkg::operation_e			fpnew_op;
logic							fpnew_op_mod;

fpnew_pkg::fp_format_e			fpnew_src_fmt;
fpnew_pkg::fp_format_e			fpnew_dst_fmt;
fpnew_pkg::int_format_e			fpnew_int_fmt;

logic							fpnew_in_valid;
logic							fpnew_in_ready;
logic [`SCR1_XLEN-1:0]			fpnew_result;
fpnew_pkg::status_t				fpnew_status;
logic							fpnew_out_valid;

// FSM
fsm_fpu_e						fsm_fpu_curr;
fsm_fpu_e						fsm_fpu_next;

logic							fpnew_done;
logic							fpnew_req;

// FPU -> FPnew conversion
logic							cmd_by_rnd;


//----------------------------------------------
// FSM 
//----------------------------------------------

always @(posedge clk) begin
	if (~rst_n) begin
		fsm_fpu_curr	<= FSM_FPU_IDLE;
	end
	else begin
		fsm_fpu_curr	<= fsm_fpu_next;
	end
end

always_comb begin
    case (fsm_fpu_curr)
		FSM_FPU_IDLE 	: begin
            if (fpnew_req)	fsm_fpu_next	= FSM_FPU_RUN;
            else			fsm_fpu_next	= FSM_FPU_IDLE;
		end
		FSM_FPU_RUN		: begin
            if (fpnew_done)	fsm_fpu_next	= FSM_FPU_IDLE;
            else			fsm_fpu_next	= FSM_FPU_RUN;
		end
        default			: fsm_fpu_next	= FSM_FPU_IDLE;
    endcase
end


assign fpnew_req		= exu2fpu_valid_i;
assign fpnew_done		= fpnew_out_valid;


//----------------------------------------------
// FPU -> FPnew conversion
//----------------------------------------------

always_comb begin
	case (exu2fpu_rnd_i)
		SCR1_FPU_RND_RNE		: fpnew_rnd_normal	= fpnew_pkg::RNE;
		SCR1_FPU_RND_RTZ		: fpnew_rnd_normal	= fpnew_pkg::RTZ;
		SCR1_FPU_RND_RDN		: fpnew_rnd_normal	= fpnew_pkg::RDN;
		SCR1_FPU_RND_RUP		: fpnew_rnd_normal	= fpnew_pkg::RUP;
		SCR1_FPU_RND_RMM		: fpnew_rnd_normal	= fpnew_pkg::RMM;
		SCR1_FPU_RND_DYN		: fpnew_rnd_normal	= fpnew_dynamic_rnd;
		default					: fpnew_rnd_normal	= fpnew_pkg::RNE;
	endcase
end

always_comb begin
	case (exu2fpu_frm_i)
		3'b000					: fpnew_dynamic_rnd	= fpnew_pkg::RNE;
		3'b001					: fpnew_dynamic_rnd	= fpnew_pkg::RTZ;
		3'b010					: fpnew_dynamic_rnd	= fpnew_pkg::RDN;
		3'b011					: fpnew_dynamic_rnd	= fpnew_pkg::RUP;
		3'b100					: fpnew_dynamic_rnd	= fpnew_pkg::RMM;
		default					: fpnew_dynamic_rnd	= fpnew_pkg::RNE;
	endcase
end

always_comb begin
	case (exu2fpu_cmd_i)
		SCR1_FPU_CMD_FSGNJ		: fpnew_rnd_for_cmd	= fpnew_pkg::RNE;
		SCR1_FPU_CMD_FSGNJN		: fpnew_rnd_for_cmd	= fpnew_pkg::RTZ;
		SCR1_FPU_CMD_FSGNJX		: fpnew_rnd_for_cmd	= fpnew_pkg::RDN;
		SCR1_FPU_CMD_FMIN		: fpnew_rnd_for_cmd	= fpnew_pkg::RNE;
		SCR1_FPU_CMD_FMAX		: fpnew_rnd_for_cmd	= fpnew_pkg::RTZ;
		SCR1_FPU_CMD_FLE		: fpnew_rnd_for_cmd = fpnew_pkg::RNE;
		SCR1_FPU_CMD_FLT		: fpnew_rnd_for_cmd = fpnew_pkg::RTZ;
		SCR1_FPU_CMD_FEQ		: fpnew_rnd_for_cmd = fpnew_pkg::RDN;
		default					: fpnew_rnd_for_cmd	= fpnew_pkg::RNE;
	endcase
end

assign	cmd_by_rnd		= ((exu2fpu_cmd_i == SCR1_FPU_CMD_FSGNJ)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FSGNJN)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FSGNJX)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FMIN)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FMAX)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FLE)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FLT)
						| (exu2fpu_cmd_i == SCR1_FPU_CMD_FEQ)
						);
assign	fpnew_rnd_mode	= (cmd_by_rnd)	? fpnew_rnd_for_cmd	: fpnew_rnd_normal;

always_comb begin
    case (exu2fpu_cmd_i)
		SCR1_FPU_CMD_FMADD		: fpnew_op	= fpnew_pkg::FMADD;
		SCR1_FPU_CMD_FMSUB		: fpnew_op	= fpnew_pkg::FMADD;
		SCR1_FPU_CMD_FNMSUB		: fpnew_op	= fpnew_pkg::FNMSUB;
		SCR1_FPU_CMD_FNMADD		: fpnew_op	= fpnew_pkg::FNMSUB;
		SCR1_FPU_CMD_FADD		: fpnew_op	= fpnew_pkg::ADD;
		SCR1_FPU_CMD_FSUB		: fpnew_op	= fpnew_pkg::ADD;
		SCR1_FPU_CMD_FMUL		: fpnew_op	= fpnew_pkg::MUL;
		SCR1_FPU_CMD_FDIV		: fpnew_op	= fpnew_pkg::DIV;
		SCR1_FPU_CMD_FSQRT		: fpnew_op	= fpnew_pkg::SQRT;
		SCR1_FPU_CMD_FSGNJ		: fpnew_op	= fpnew_pkg::SGNJ;
		SCR1_FPU_CMD_FSGNJN		: fpnew_op	= fpnew_pkg::SGNJ;
		SCR1_FPU_CMD_FSGNJX		: fpnew_op	= fpnew_pkg::SGNJ;
		SCR1_FPU_CMD_FMIN		: fpnew_op	= fpnew_pkg::MINMAX;
		SCR1_FPU_CMD_FMAX		: fpnew_op	= fpnew_pkg::MINMAX;
		SCR1_FPU_CMD_FCVT_F2F	: fpnew_op	= fpnew_pkg::F2F;
		SCR1_FPU_CMD_FCVT_F2I	: fpnew_op	= fpnew_pkg::F2I;
		SCR1_FPU_CMD_FCVT_F2UI	: fpnew_op	= fpnew_pkg::F2I;
		SCR1_FPU_CMD_FCVT_I2F	: fpnew_op	= fpnew_pkg::I2F;
		SCR1_FPU_CMD_FCVT_UI2F	: fpnew_op	= fpnew_pkg::I2F;
		SCR1_FPU_CMD_FEQ		: fpnew_op	= fpnew_pkg::CMP;
		SCR1_FPU_CMD_FLT		: fpnew_op	= fpnew_pkg::CMP;
		SCR1_FPU_CMD_FLE		: fpnew_op	= fpnew_pkg::CMP;
		SCR1_FPU_CMD_FCLASS		: fpnew_op	= fpnew_pkg::CLASSIFY;
		default					: fpnew_op	= fpnew_pkg::CLASSIFY;
    endcase
end

always_comb begin
    case (exu2fpu_cmd_i)
		SCR1_FPU_CMD_FMADD		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FMSUB		: fpnew_op_mod	= 1'b1; 
		SCR1_FPU_CMD_FNMSUB		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FNMADD		: fpnew_op_mod	= 1'b1; 
		SCR1_FPU_CMD_FADD		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FSUB		: fpnew_op_mod	= 1'b1; 
		SCR1_FPU_CMD_FMUL		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FDIV		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FSQRT		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FSGNJ		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FSGNJN		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FSGNJX		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FMIN		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FMAX		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FCVT_F2F	: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FCVT_F2I	: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FCVT_F2UI	: fpnew_op_mod	= 1'b1; 
		SCR1_FPU_CMD_FCVT_I2F	: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FCVT_UI2F	: fpnew_op_mod	= 1'b1; 
		SCR1_FPU_CMD_FEQ		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FLT		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FLE		: fpnew_op_mod	= 1'b0; 
		SCR1_FPU_CMD_FCLASS		: fpnew_op_mod	= 1'b0; 
		default					: fpnew_op_mod	= 1'b0; 
    endcase
end

always_comb begin
	case (exu2fpu_src_fmt_i)
		SCR1_FPU_FMT_F32		: fpnew_src_fmt	= fpnew_pkg::FP32;
		SCR1_FPU_FMT_F64		: fpnew_src_fmt	= fpnew_pkg::FP64;
		default					: fpnew_src_fmt	= fpnew_pkg::FP64;
	endcase
end

always_comb begin
	case (exu2fpu_dst_fmt_i)
		SCR1_FPU_FMT_F32		: fpnew_dst_fmt	= fpnew_pkg::FP32;
		SCR1_FPU_FMT_F64		: fpnew_dst_fmt	= fpnew_pkg::FP64;
		default					: fpnew_dst_fmt	= fpnew_pkg::FP64;
	endcase
end

always_comb begin
	case (exu2fpu_int_fmt_i)
		SCR1_FPU_FMT_I32		: fpnew_int_fmt	= fpnew_pkg::INT32;
		SCR1_FPU_FMT_I64		: fpnew_int_fmt	= fpnew_pkg::INT64;
		default					: fpnew_int_fmt	= fpnew_pkg::INT64;
	endcase
end

always_comb begin
	case (exu2fpu_cmd_i)
		SCR1_FPU_CMD_FADD,
		SCR1_FPU_CMD_FSUB		: begin
			fpnew_operands[0]	= '0;
			fpnew_operands[1]	= exu2fpu_main_op1_i;
			fpnew_operands[2]	= exu2fpu_main_op2_i;
		end
		SCR1_FPU_CMD_FCVT_I2F,
		SCR1_FPU_CMD_FCVT_UI2F	: begin
			fpnew_operands[0]	= exu2fpu_int_op_i;
			fpnew_operands[1]	= '0;
			fpnew_operands[2]	= '0;
		end
		default					: begin
			fpnew_operands[0]	= exu2fpu_main_op1_i;
			fpnew_operands[1]	= exu2fpu_main_op2_i;
			fpnew_operands[2]	= exu2fpu_main_op3_i;
		end
	endcase
end


//----------------------------------------------
// fpnew instansiation
//----------------------------------------------

fpnew_top #(
	.Features		(fpnew_pkg::RV64D			),
//	.Implementation	(fpnew_pkg::DEFAULT_NOREGS	)
	.Implementation	(FPU_IMP_REGS_1				)
) i_fpnew_top (
	.clk_i			(clk				),
	.rst_ni			(rst_n				),

	.operands_i		(fpnew_operands		),
	.rnd_mode_i		(fpnew_rnd_mode		),
	.op_i			(fpnew_op			),
	.op_mod_i		(fpnew_op_mod		),
	.src_fmt_i		(fpnew_src_fmt		),
	.dst_fmt_i		(fpnew_dst_fmt		),
	.int_fmt_i		(fpnew_int_fmt		),
	.vectorial_op_i	(1'b0				),
	.tag_i			(1'b0				),

	.in_valid_i		(fpnew_in_valid		),
	.in_ready_o		(fpnew_in_ready		),
	.flush_i		(1'b0				),

	.result_o		(fpnew_result		),
	.status_o		(fpnew_status		),
	.tag_o			(					),

	.out_valid_o	(fpnew_out_valid	),
	.out_ready_i	(1'b1				),

	.busy_o			(					)
);


assign fpnew_in_valid		= (fpnew_req & (fsm_fpu_curr == FSM_FPU_IDLE));

assign fpu2exu_ready_o		= fpnew_out_valid;
assign fpu2exu_result_o		= fpnew_result;
assign fpu2exu_status_o		= {fpnew_status.NV, fpnew_status.DZ, fpnew_status.OF, fpnew_status.UF, fpnew_status.NX};

endmodule
