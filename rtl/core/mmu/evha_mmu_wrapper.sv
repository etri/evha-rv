// Copyright (c) 2025 ETRI
//
// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of EVHA-RV and is distributed under the terms of
// the GNU General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
// See the LICENSE file for details; there is NO WARRANTY, to the extent permitted by law.
//
// @file   evha_mmu_wrapper.sv
// @brief  mmu wrapper for ehva-rv

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"

module evha_mmu_wrapper (
	input	logic						rst_n,
	input	logic						clk,

    input 	logic 						csr2mmu_trans_instr_i,
    input 	logic 						csr2mmu_trans_ldst_i,  // enable virtual memory translation for load/stores

	// MMU - IFU interface
	input	logic						ifu2mmu_req_i,
	input	logic [`SCR1_XLEN-1:0]		ifu2mmu_vaddr_i,
	input	logic						ifu2mmu_new_pc_i,

	output	logic						mmu2imem_req_o,
	output	logic [`SCR1_XLEN-1:0]		mmu2imem_addr_o,
	output	logic						mmu2ifu_exc_o,
	output	type_scr1_exc_code_e		mmu2ifu_exc_code_o,

	// MMU - EXU interface
	input	logic						exu2mmu_lsu_req_i,
    input 	logic [`SCR1_XLEN-1:0] 		exu2mmu_lsu_vaddr_i,  // virtual address in
	input	type_scr1_lsu_cmd_sel_e		exu2mmu_lsu_cmd_i,
	input	logic [`SCR1_XLEN-1:0]		exu2mmu_vaddr_flush_i,
	input	logic [`SCR1_XLEN-1:0]		exu2mmu_asid_flush_i,

	// MMU - LSU interface (address translation)
	output 	logic 						mmu2lsu_dtlb_hit_o,  // sent in same cycle as the request if translation hits in DTLB
    output 	logic [44-1:0] 				mmu2lsu_dtlb_ppn_o,  // ppn (send same cycle as hit)
	
    output 	logic 						mmu2lsu_valid_o,  // translation is valid
    output 	logic [`SCR1_XLEN-1:0] 		mmu2lsu_paddr_o,  // translated address
    output 	logic 						mmu2lsu_exception_o,  // address translation threw an exception
    output 	type_scr1_exc_code_e		mmu2lsu_exc_code_o,  // address translation threw an exception

	// MMU - DMEM interface (page table walking)
	output	logic						mmu2dmem_req_o,
	output	type_scr1_mem_cmd_e			mmu2dmem_cmd_o,
	output	logic [`SCR1_XLEN-1:0]		mmu2dmem_addr_o,
	input	logic						dmem2mmu_rdy_i,
	input	logic [`SCR1_XLEN-1:0]		dmem2mmu_ldata_i,
	input	logic						dmem2mmu_exc_i,

	// MMU - CSR interface
	input	logic [1:0]					csr2mmu_priv_instr_i,
	input	logic [1:0]					csr2mmu_priv_ldst_i,
	input	logic						csr2mmu_sum_i,
	input	logic						csr2mmu_mxr_i,

    input 	logic [44-1:0]				csr2mmu_ppn_i,

    input 	logic [16-1:0] 				csr2mmu_asid_i,

	input	logic						exu2mmu_flush_tlb_i
);

parameter cva6_cfg_t mmu_cfg = '{
	XLEN					: `SCR1_XLEN,
	VLEN					: `SCR1_XLEN,
	PLEN					: `SCR1_XLEN,
	GPLEN					: `SCR1_XLEN,
	IS_XLEN64				: 1,
	ASID_WIDTH				: 16,
	VMID_WIDTH				: 14,
	
	NrPMPEntries			: 8,
	PtLevels				: 3,
	VpnLen					: 27,
	InstrTlbEntries			: 16,
	DataTlbEntries			: 16,
	UseSharedTlb			: 0,
	SharedTlbDepth			: 64,

	RVH						: 0,

	PPNW					: 44,
	GPPNW					: 29,
	SV						: 39,

	TvalEn					: 1,

	ICACHE_INDEX_WIDTH		: `SCR1_IMEM_AWIDTH - 1,
	ICACHE_TAG_WIDTH		: 1,
	DCACHE_INDEX_WIDTH		: `SCR1_DMEM_AWIDTH - 1,
	DCACHE_TAG_WIDTH		: 1,
	DCACHE_USER_WIDTH		: `SCR1_DMEM_DWIDTH,
	DcacheIdWidth			: 1
};

typedef enum logic {
	MMU_IMEM_ADDR_IDLE,
	MMU_IMEM_ADDR_WAIT
} type_mmu_imem_fsm_e;

typedef struct packed {
      logic [mmu_cfg.XLEN-1:0] cause;  // cause of exception
      logic [mmu_cfg.XLEN-1:0] tval;  // additional information of causing exception (e.g.: instruction causing it), address of LD/ST fault
      logic [mmu_cfg.GPLEN-1:0] tval2;  // additional information when the causing exception in a guest exception
      logic [31:0] tinst;  // transformed instruction information
      logic gva;  // signals when a guest virtual address is written to tval
      logic valid;
} exception_t;

typedef struct packed {
	logic                    fetch_valid;      // address translation valid
	logic [mmu_cfg.PLEN-1:0] fetch_paddr;      // physical address in
	exception_t              fetch_exception;  // exception occurred during fetch
} icache_areq_t; 

typedef struct packed {
	logic                    fetch_req;    // address translation request
	logic [mmu_cfg.VLEN-1:0] fetch_vaddr;  // virtual address out
} icache_arsp_t; 

typedef struct packed {
	logic [mmu_cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
	logic [mmu_cfg.DCACHE_TAG_WIDTH-1:0]   address_tag;
	logic [mmu_cfg.XLEN-1:0]               data_wdata;
	logic [mmu_cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
	logic                                  data_req;
	logic                                  data_we;
	logic [(mmu_cfg.XLEN/8)-1:0]           data_be;
	logic [1:0]                            data_size;
	logic [mmu_cfg.DcacheIdWidth-1:0]      data_id;
	logic                                  kill_req;
	logic                                  tag_valid;
} dcache_req_i_t; // only for PTW

typedef struct packed {
	logic                                 data_gnt;
	logic                                 data_rvalid;
	logic [mmu_cfg.DcacheIdWidth-1:0]     data_rid;
	logic [mmu_cfg.XLEN-1:0]              data_rdata;
	logic [mmu_cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
} dcache_req_o_t; // only for PTW

exception_t		misaligned_ex;
exception_t		mmu_exception;

icache_areq_t	mmu2imem_req;
icache_arsp_t	core2mmu_rsp;
dcache_req_i_t	mmu2dmem_req;
dcache_req_o_t	dmem2mmu_rsp;


assign misaligned_ex.cause	= '0;
assign misaligned_ex.tval	= '0;
assign misaligned_ex.tval2	= '0;
assign misaligned_ex.tinst	= '0;
assign misaligned_ex.gva	= '0;
assign misaligned_ex.valid	= '0;


assign mmu2ifu_exc_o		= mmu2imem_req.fetch_exception.valid;
assign mmu2ifu_exc_code_o	= mmu2imem_req.fetch_exception.cause;

assign mmu2imem_req_o		= mmu2imem_req.fetch_valid;
assign mmu2imem_addr_o		= mmu2imem_req.fetch_paddr;

assign core2mmu_rsp.fetch_req	= ifu2mmu_req_i & ~ifu2mmu_new_pc_i;
assign core2mmu_rsp.fetch_vaddr	= ifu2mmu_vaddr_i; 




assign mmu2lsu_exception_o	= mmu_exception.valid;
assign mmu2lsu_exc_code_o	= mmu_exception.cause;


assign mmu2dmem_req_o	= mmu2dmem_req.data_req;
assign mmu2dmem_cmd_o	= (mmu2dmem_req.data_we)	? SCR1_MEM_CMD_WR : SCR1_MEM_CMD_RD;
assign mmu2dmem_addr_o	= {mmu2dmem_req.address_tag, mmu2dmem_req.address_index};

assign dmem2mmu_rsp.data_rvalid		= dmem2mmu_rdy_i;
assign dmem2mmu_rsp.data_rdata		= dmem2mmu_ldata_i;
assign dmem2mmu_rsp.data_gnt		= dmem2mmu_rdy_i;
assign dmem2mmu_rsp.data_rid		= '0;
assign dmem2mmu_rsp.data_ruser		= '0;



type_mmu_imem_fsm_e		mmu_fsm_ff;
type_mmu_imem_fsm_e		mmu_fsm_next;

always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		mmu_fsm_ff	<= MMU_IMEM_ADDR_IDLE;
	end
	else begin
		mmu_fsm_ff	<= mmu_fsm_next;
	end
end

always_comb begin
	case (1'b1)
		(mmu_fsm_ff == MMU_IMEM_ADDR_IDLE) & ifu2mmu_req_i	: mmu_fsm_next	= MMU_IMEM_ADDR_WAIT;
		(mmu_fsm_ff == MMU_IMEM_ADDR_WAIT) & ifu2mmu_req_i	: mmu_fsm_next	= MMU_IMEM_ADDR_WAIT;
		(mmu_fsm_ff == MMU_IMEM_ADDR_WAIT) & mmu2imem_req_o	: mmu_fsm_next	= MMU_IMEM_ADDR_IDLE;
		default												: mmu_fsm_next	= mmu_fsm_ff;
	endcase
end


logic 			exu2mmu_lsu_is_store;

cva6_mmu #(
	.CVA6Cfg		(mmu_cfg			),
	.icache_areq_t  (icache_areq_t		),
	.icache_arsp_t  (icache_arsp_t		),
	.dcache_req_i_t (dcache_req_i_t		),
	.dcache_req_o_t (dcache_req_o_t		),
	.exception_t    (exception_t		),
	.HYP_EXT        (0					)
) i_cva6_mmu
(
    .clk_i						(clk						),
    .rst_ni						(rst_n						),
    .flush_i					(1'b0						),
    .enable_translation_i		(csr2mmu_trans_instr_i		),
    .en_ld_st_translation_i		(csr2mmu_trans_ldst_i		),  // enable virtual memory translation for load/stores

	// IF interface
    .icache_areq_i				(core2mmu_rsp			),
    .icache_areq_o				(mmu2imem_req			),

	// LSU interface
    // this is a more minimalistic interface because the actual addressing logic is handled
    // in the LSU as we distinguish load and stores, what we do here is simple address translation
    .misaligned_ex_i			(misaligned_ex			),	// misaligned
    .lsu_req_i					(exu2mmu_lsu_req_i		),  // request address translation
    .lsu_vaddr_i				(exu2mmu_lsu_vaddr_i	),  // virtual address in
    .lsu_is_store_i				(exu2mmu_lsu_is_store	),  // the translation is requested by a store
    // if we need to walk the page table we can't grant in the same cycle

	// Cycle 0
    .lsu_dtlb_hit_o				(mmu2lsu_dtlb_hit_o		),  // sent in same cycle as the request if translation hits in DTLB
    .lsu_dtlb_ppn_o				(mmu2lsu_dtlb_ppn_o		),  // ppn (send same cycle as hit)

	// Cycle 1
    .lsu_valid_o				(mmu2lsu_valid_o		),  // translation is valid
    .lsu_paddr_o				(mmu2lsu_paddr_o		),  // translated address
    .lsu_exception_o			(mmu_exception			),  // address translation threw an exception

	// General control signals
    .priv_lvl_i					(csr2mmu_priv_instr_i	),
    .ld_st_priv_lvl_i			(csr2mmu_priv_ldst_i	),
    .sum_i						(csr2mmu_sum_i			),
    .mxr_i						(csr2mmu_mxr_i			),

    .satp_ppn_i					(csr2mmu_ppn_i			),

    .asid_i						(csr2mmu_asid_i			),
    .asid_to_be_flushed_i		(exu2mmu_asid_flush_i	),
    .vaddr_to_be_flushed_i		(exu2mmu_vaddr_flush_i	),

    .flush_tlb_i				(exu2mmu_flush_tlb_i	),

    // Performance counters
    .itlb_miss_o				(						),
    .dtlb_miss_o				(						),

	// PTW memory interface
    .req_port_i					(dmem2mmu_rsp			),
    .req_port_o					(mmu2dmem_req			),


	// H-extension values
    .enable_g_translation_i		('0						),
    .en_ld_st_g_translation_i	('0						),  // enable G-Stage translation for load/stores
    .lsu_tinst_i				('0						),  // transformed instruction in
    .csr_hs_ld_st_inst_o		(						),  // hyp load store instruction
    .v_i						('0						),	// H-extension	
    .ld_st_v_i					('0						),	// H-extension	
    .vs_sum_i					('0						),	// H-extension	
    .vmxr_i						('0						),	// H-extension	
    .hlvx_inst_i				('0						),	// H-extension
    .hs_ld_st_inst_i			('0						),	// H-extension
    .vsatp_ppn_i				('0						),	// H-extension
    .hgatp_ppn_i				('0						),	// H-extension
    .vs_asid_i					('0						),	// H-extension
    .vmid_i						('0						),	// H-extension
    .vmid_to_be_flushed_i		('0						),	// H-extension
    .gpaddr_to_be_flushed_i		('0						),	// H-extension
    .flush_tlb_vvma_i			('0						),	// H-extension
    .flush_tlb_gvma_i			('0						)	// H-extension
);

assign exu2mmu_lsu_is_store		= (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SB )
			                    | (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SH )
			                    | (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SW )
			                    | (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SD )
			                    | (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_FSW)
			                    | (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_FSD)
							 	| (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SW)
							  	| (exu2mmu_lsu_cmd_i == SCR1_LSU_CMD_SD);

endmodule
