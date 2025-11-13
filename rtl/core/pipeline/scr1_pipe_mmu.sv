// Copyright (c) 2025 ETRI
//
// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of EVHA-RV and is distributed under the terms of
// the GNU General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
// See the LICENSE file for details; there is NO WARRANTY, to the extent permitted by law.
//
// @file   scr1_pipe_mmu.sv
// @brief  Additional pipeline stage with MMU

`include "scr1_memif.svh"
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_arch_description.svh"

module scr1_pipe_bdg
(
    input   logic                               	rst_n,                      // EXU reset
    input   logic                               	clk,                        // Gated EXU clock

    // Instruction Memory Interface
    input  	logic									pipe2bdg_imem_req_i,            // IMEM request
    input  	type_scr1_mem_cmd_e						pipe2bdg_imem_cmd_i,            // IMEM command
    input  	logic [`SCR1_XLEN-1:0]					pipe2bdg_imem_addr_i,           // IMEM address
	input	logic									pipe2bdg_imem_new_pc_i,
    output 	logic									bdg2pipe_imem_req_ack_o,        // IMEM request acknowledge
    output 	logic [`SCR1_IMEM_DWIDTH-1:0]			bdg2pipe_imem_rdata_o,          // IMEM read data
    output 	type_scr1_mem_resp_e					bdg2pipe_imem_resp_o,           // IMEM response

    output 	logic									bdg2imem_req_o,            // IMEM request
    output 	type_scr1_mem_cmd_e						bdg2imem_cmd_o,            // IMEM command
    output 	logic [`SCR1_IMEM_AWIDTH-1:0]			bdg2imem_addr_o,           // IMEM address
    input  	logic									imem2bdg_req_ack_i,        // IMEM request acknowledge
    input  	logic [`SCR1_IMEM_DWIDTH-1:0]			imem2bdg_rdata_i,          // IMEM read data
    input	type_scr1_mem_resp_e					imem2bdg_resp_i,           // IMEM response


    // Data Memory Interface
    input  	logic									pipe2bdg_dmem_req_i,            // DMEM request
    input  	type_scr1_mem_cmd_e						pipe2bdg_dmem_cmd_i,            // DMEM command
    input  	type_scr1_mem_width_e					pipe2bdg_dmem_width_i,          // DMEM data width
    input  	logic [`SCR1_XLEN-1:0]					pipe2bdg_dmem_addr_i,           // DMEM address
    input  	logic [`SCR1_DMEM_DWIDTH-1:0]			pipe2bdg_dmem_wdata_i,          // DMEM write data
    output  logic									bdg2pipe_dmem_req_ack_o,        // DMEM request acknowledge
    output  logic [`SCR1_DMEM_DWIDTH-1:0]			bdg2pipe_dmem_rdata_o,          // DMEM read data
    output  type_scr1_mem_resp_e					bdg2pipe_dmem_resp_o,           // DMEM response

    output  logic									bdg2dmem_req_o,            // DMEM request
    output  type_scr1_mem_cmd_e						bdg2dmem_cmd_o,            // DMEM command
    output  type_scr1_mem_width_e					bdg2dmem_width_o,          // DMEM data width
    output  logic [`SCR1_DMEM_AWIDTH-1:0]			bdg2dmem_addr_o,           // DMEM address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]			bdg2dmem_wdata_o,          // DMEM write data
    input   logic									dmem2bdg_req_ack_i,        // DMEM request acknowledge
    input   logic [`SCR1_DMEM_DWIDTH-1:0]			dmem2bdg_rdata_i,          // DMEM read data
    input   type_scr1_mem_resp_e					dmem2bdg_resp_i,           // DMEM response

	// MMU <-> Bridge interface
	input	logic									csr2bdg_trans_instr_i,
	input	logic									csr2bdg_trans_ldst_i,

	input	logic									mmu2bdg_imem_req_i,
	input	logic [`SCR1_XLEN-1:0]					mmu2bdg_imem_addr_i,
	input	logic									mmu2bdg_imem_exc_i,

	input	logic									mmu2bdg_dmem_req_i,
	input	type_scr1_mem_cmd_e						mmu2bdg_dmem_cmd_i,
	input	logic [`SCR1_XLEN-1:0]					mmu2bdg_dmem_addr_i,
	output	logic									bdg2mmu_dmem_rdy_o,
	output	logic [`SCR1_XLEN-1:0]					bdg2mmu_dmem_ldata_o,
	output	logic									bdg2mmu_dmem_exc_o
);


typedef enum logic [1:0] {
	MMU_IMEM_IDLE,
	MMU_IMEM_ADDR_FAULT,
	MMU_IMEM_WAITING_MMU
} type_mmu_imem_fsm_e;

typedef enum logic [1:0] {
	MMU_DMEM_IDLE,
	MMU_DMEM_ADDR_FAULT,
	MMU_DMEM_WAITING_LSU,
	MMU_DMEM_WAITING_PTW
} type_mmu_dmem_fsm_e;


logic					imem_vd;
logic					dmem_vd;


logic					imem_addr_fault;
logic					imem_addr_fault_ff;

logic					dmem_addr_fault;
logic					dmem_addr_fault_ff;

logic					imem_addr_valid;
logic					dmem_addr_valid;

logic					mmu_imem_ptw_on;
logic					mmu_imem_ptw_done;


type_mmu_imem_fsm_e		mmu_imem_fsm_ff;
type_mmu_imem_fsm_e		mmu_imem_fsm_next;

type_mmu_dmem_fsm_e		mmu_dmem_fsm_ff;
type_mmu_dmem_fsm_e		mmu_dmem_fsm_next;


assign dmem_vd		=	(dmem2bdg_resp_i == SCR1_MEM_RESP_RDY_OK);



always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		imem_addr_fault_ff	<= '0;
		dmem_addr_fault_ff	<= '0;
	end
	else begin
		imem_addr_fault_ff	<= imem_addr_fault;
		dmem_addr_fault_ff	<= dmem_addr_fault;
	end
end

assign	imem_addr_fault		= pipe2bdg_imem_req_i & ~imem_addr_valid;
assign	dmem_addr_fault		= pipe2bdg_dmem_req_i & ~dmem_addr_valid;

assign	imem_addr_valid		= ((pipe2bdg_imem_addr_i & SCR1_IMEM_ADDR_MASK) == SCR1_IMEM_ADDR_PATTERN);
assign	dmem_addr_valid		= ((pipe2bdg_dmem_addr_i & SCR1_DMEM_ADDR_MASK) == SCR1_DMEM_ADDR_PATTERN)
							| ((pipe2bdg_dmem_addr_i & SCR1_TIMER_ADDR_MASK) == SCR1_TIMER_ADDR_PATTERN)
							| ((pipe2bdg_dmem_addr_i & SCR1_PRINT_ADDR_MASK) == SCR1_PRINT_ADDR_PATTERN);

//assign		imem_addr_valid		= 1'b1;
//assign		dmem_addr_valid		= 1'b1;


// IMEM interface
always_comb begin
	case (1'b1)
		imem_addr_fault			: begin
			bdg2imem_req_o		= 1'b0;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= '0;
		end
		/*
		(mmu_imem_ptw_on)		: begin
			bdg2imem_req_o		= 1'b0;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= '0;
		end
		csr2bdg_trans_instr_i & (mmu_imem_fsm_ff == MMU_IMEM_WAITING_MMU)	: begin
			bdg2imem_req_o		= 1'b0;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= '0;
		end
		csr2bdg_trans_instr_i & (mmu_imem_fsm_ff == MMU_IMEM_IDLE)	: begin
			bdg2imem_req_o		= mmu2bdg_imem_req_i;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= mmu2bdg_imem_addr_i;
		end
		*/
		csr2bdg_trans_instr_i & mmu_imem_ptw_on		: begin
			bdg2imem_req_o		= 1'b0;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= '0;
		end
		csr2bdg_trans_instr_i & ~mmu_imem_ptw_on	:begin
			bdg2imem_req_o		= mmu2bdg_imem_req_i;
			bdg2imem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2imem_addr_o		= mmu2bdg_imem_addr_i;
		end
		default					: begin
			bdg2imem_req_o		= pipe2bdg_imem_req_i;
			bdg2imem_cmd_o		= pipe2bdg_imem_cmd_i;
			bdg2imem_addr_o		= pipe2bdg_imem_addr_i[`SCR1_IMEM_AWIDTH-1:0];
		end
	endcase
end

always_comb begin
	case (1'b1)
		(mmu_imem_fsm_ff == MMU_IMEM_ADDR_FAULT)	: begin
			bdg2pipe_imem_req_ack_o		= 1'b1;
			bdg2pipe_imem_rdata_o		= '0;
			bdg2pipe_imem_resp_o		= SCR1_MEM_RESP_RDY_ER;
		end
		/*
		(mmu_imem_ptw_on)							: begin
			bdg2pipe_imem_req_ack_o		= 1'b0;
			bdg2pipe_imem_rdata_o		= '0;
			bdg2pipe_imem_resp_o		= SCR1_MEM_RESP_NOTRDY;
		end
		(mmu_imem_fsm_ff == MMU_IMEM_WAITING_MMU)	: begin
			bdg2pipe_imem_req_ack_o		= 1'b0;
			bdg2pipe_imem_rdata_o		= '0;
			bdg2pipe_imem_resp_o		= SCR1_MEM_RESP_NOTRDY;
		end
		*/
		csr2bdg_trans_instr_i & mmu_imem_ptw_on		: begin
			bdg2pipe_imem_req_ack_o		= 1'b0;
			bdg2pipe_imem_rdata_o		= imem2bdg_rdata_i;
			bdg2pipe_imem_resp_o		= imem2bdg_resp_i;
		end
		default										: begin
			bdg2pipe_imem_req_ack_o		= imem2bdg_req_ack_i;
			bdg2pipe_imem_rdata_o		= imem2bdg_rdata_i;
			bdg2pipe_imem_resp_o		= imem2bdg_resp_i;
		end
	endcase
end


always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		mmu_imem_fsm_ff	<= MMU_IMEM_IDLE;
	end
	else begin
		mmu_imem_fsm_ff	<= mmu_imem_fsm_next;
	end
end

always_comb begin
	case (1'b1)
		(mmu_imem_fsm_ff == MMU_IMEM_IDLE) & imem_addr_fault			: mmu_imem_fsm_next	= MMU_IMEM_ADDR_FAULT;
		(mmu_imem_fsm_ff == MMU_IMEM_IDLE) & pipe2bdg_imem_new_pc_i		: mmu_imem_fsm_next	= MMU_IMEM_IDLE;
		(mmu_imem_fsm_ff == MMU_IMEM_IDLE) & mmu_imem_ptw_on			: mmu_imem_fsm_next	= MMU_IMEM_WAITING_MMU;
		(mmu_imem_fsm_ff == MMU_IMEM_ADDR_FAULT) & imem_addr_fault		: mmu_imem_fsm_next	= MMU_IMEM_ADDR_FAULT;
		(mmu_imem_fsm_ff == MMU_IMEM_ADDR_FAULT) & ~imem_addr_fault		: mmu_imem_fsm_next	= MMU_IMEM_IDLE;
		(mmu_imem_fsm_ff == MMU_IMEM_WAITING_MMU) & mmu_imem_ptw_done	: mmu_imem_fsm_next	= MMU_IMEM_IDLE;
		default															: mmu_imem_fsm_next	= mmu_imem_fsm_ff;
	endcase
end

assign mmu_imem_ptw_on		= csr2bdg_trans_instr_i 
							& pipe2bdg_imem_req_i 
							& ~mmu2bdg_imem_req_i;
assign mmu_imem_ptw_done	= mmu2bdg_imem_req_i;


// DMEM interface
always_comb begin
	case (1'b1)
		dmem_addr_fault				: begin
			bdg2dmem_req_o		= 1'b0;
			bdg2dmem_cmd_o		= SCR1_MEM_CMD_RD;
			bdg2dmem_width_o	= SCR1_MEM_WIDTH_BYTE;
			bdg2dmem_addr_o		= '0;
			bdg2dmem_wdata_o	= '0;
		end
		mmu2bdg_dmem_req_i			: begin
			bdg2dmem_req_o		= mmu2bdg_dmem_req_i;
			bdg2dmem_cmd_o		= mmu2bdg_dmem_cmd_i;
			bdg2dmem_width_o	= SCR1_MEM_WIDTH_DWORD;
			bdg2dmem_addr_o		= mmu2bdg_dmem_addr_i;
			bdg2dmem_wdata_o	= '0;
		end
		default						: begin
			bdg2dmem_req_o		= pipe2bdg_dmem_req_i;
			bdg2dmem_cmd_o		= pipe2bdg_dmem_cmd_i;
			bdg2dmem_width_o	= pipe2bdg_dmem_width_i;
			bdg2dmem_addr_o		= pipe2bdg_dmem_addr_i[`SCR1_DMEM_AWIDTH-1:0];
			bdg2dmem_wdata_o	= pipe2bdg_dmem_wdata_i;
		end
	endcase
end

always_comb begin
	case (1'b1)
		(mmu_dmem_fsm_ff == MMU_DMEM_ADDR_FAULT)		: begin
			bdg2pipe_dmem_req_ack_o		= 1'b1;
			bdg2pipe_dmem_rdata_o		= '0;
			bdg2pipe_dmem_resp_o		= SCR1_MEM_RESP_RDY_ER;
		end
		(mmu_dmem_fsm_ff == MMU_DMEM_WAITING_PTW)		: begin
			bdg2pipe_dmem_req_ack_o		= 1'b0;
			bdg2pipe_dmem_rdata_o		= '0;
			bdg2pipe_dmem_resp_o		= SCR1_MEM_RESP_NOTRDY;
		end
		default											: begin
			bdg2pipe_dmem_req_ack_o		= dmem2bdg_req_ack_i;
			bdg2pipe_dmem_rdata_o		= dmem2bdg_rdata_i;
			bdg2pipe_dmem_resp_o		= dmem2bdg_resp_i;
		end
	endcase
end

always_comb begin
	case (1'b1)
		(mmu_dmem_fsm_ff == MMU_DMEM_WAITING_PTW)		: begin
			bdg2mmu_dmem_rdy_o				= dmem_vd;
			bdg2mmu_dmem_ldata_o			= dmem2bdg_rdata_i;
			bdg2mmu_dmem_exc_o				= (dmem2bdg_resp_i == SCR1_MEM_RESP_RDY_ER);
		end
		default						: begin
			bdg2mmu_dmem_rdy_o				= 1'b0;
			bdg2mmu_dmem_ldata_o			= '0;
			bdg2mmu_dmem_exc_o				= '0;
		end
	endcase
end



always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		mmu_dmem_fsm_ff	<= MMU_DMEM_IDLE;
	end
	else begin
		mmu_dmem_fsm_ff	<= mmu_dmem_fsm_next;
	end
end

always_comb begin
	case (1'b1)
		(mmu_dmem_fsm_ff == MMU_DMEM_IDLE) & dmem_addr_fault		: mmu_dmem_fsm_next	= MMU_DMEM_ADDR_FAULT;
//		(mmu_dmem_fsm_ff == MMU_DMEM_IDLE) & pipe2bdg_dmem_req_i	: mmu_dmem_fsm_next	= MMU_DMEM_WAITING_LSU;
		(mmu_dmem_fsm_ff == MMU_DMEM_IDLE) & mmu2bdg_dmem_req_i		: mmu_dmem_fsm_next	= MMU_DMEM_WAITING_PTW;
		(mmu_dmem_fsm_ff == MMU_DMEM_ADDR_FAULT) & dmem_addr_fault	: mmu_dmem_fsm_next	= MMU_DMEM_ADDR_FAULT;
		(mmu_dmem_fsm_ff == MMU_DMEM_ADDR_FAULT) & ~dmem_addr_fault	: mmu_dmem_fsm_next	= MMU_DMEM_IDLE;
//		(mmu_dmem_fsm_ff == MMU_DMEM_WAITING_LSU) & dmem_vd			: mmu_dmem_fsm_next	= MMU_DMEM_IDLE;
		(mmu_dmem_fsm_ff == MMU_DMEM_WAITING_PTW) & dmem_vd			: mmu_dmem_fsm_next	= MMU_DMEM_IDLE;
		default														: mmu_dmem_fsm_next	= mmu_dmem_fsm_ff;
	endcase
end


endmodule : scr1_pipe_bdg

