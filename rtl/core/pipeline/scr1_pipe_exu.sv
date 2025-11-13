/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_pipe_exu.sv>
/// @brief      Execution Unit (EXU)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Performs instructions execution:
 //   - Prevents instructions from execution if the HART is in WFI or Debug Halted
 //     state
 //   - Fetches operands for IALU
 //   - Calculates operation results via IALU
 //   - Stores IALU results in MPRF
 //   - Performs LOAD/STORE operations via LSU
 // - Handles exceptions:
 //   - Generates exception request
 //   - Encodes exception code
 //   - Calculates exception trap value
 // - Controls WFI instruction execution
 // - Calculates PC value:
 //   - Initializes PC on reset
 //   - Stores the current PC value
 //   - Calculates a New PC value and generates a New PC request to IFU
 //
 // Structure:
 // - Instruction queue
 // - Integer Arithmetic Logic Unit (IALU)
 // - Exceptions logic
 // - WFI logic
 // - Program Counter logic
 // - Load-Store Unit (LSU)
 // - EXU status logic
 // - EXU <-> MPRF i/f
 // - EXU <-> CSR i/f
 // - EXU <-> TDU i/f
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_csr.svh"

`ifdef SCR1_DBG_EN
 `include "scr1_hdu.svh"
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
 `include "scr1_tdu.svh"
`endif // SCR1_TDU_EN

module scr1_pipe_exu (
    // Common
    input   logic                               rst_n,                      // EXU reset
    input   logic                               clk,                        // Gated EXU clock
`ifdef SCR1_CLKCTRL_EN
    input   logic                               clk_alw_on,                 // Not-gated EXU clock
    input   logic                               clk_pipe_en,                // EXU clock enabled flag
`endif // SCR1_CLKCTRL_EN

    // EXU <-> IDU interface
    input   logic                               idu2exu_req_i,              // Request form IDU to EXU
    output  logic                               exu2idu_rdy_o,              // EXU ready for new data from IDU
    input   type_scr1_exu_cmd_s                 idu2exu_cmd_i,              // EXU command
    input   logic                               idu2exu_use_rs1_i,          // Clock gating on rs1_addr field
    input   logic                               idu2exu_use_rs2_i,          // Clock gating on rs2_addr field
    input   logic                               idu2exu_use_rs3_i,          // Clock gating on rs3_addr field
`ifndef SCR1_NO_EXE_STAGE
    input   logic                               idu2exu_use_rd_i,           // Clock gating on rd_addr field
    input   logic                               idu2exu_use_imm_i,          // Clock gating on imm field
`endif // SCR1_NO_EXE_STAGE

    // EXU <-> MPRF interface
    output  logic [`SCR1_MPRF_AWIDTH-1:0]       exu2mprf_rs1_addr_o,        // MPRF rs1 read address
    input   logic [`SCR1_XLEN-1:0]              mprf2exu_rs1_data_i,        // MPRF rs1 read data
    output  logic [`SCR1_MPRF_AWIDTH-1:0]       exu2mprf_rs2_addr_o,        // MPRF rs2 read address
    input   logic [`SCR1_XLEN-1:0]              mprf2exu_rs2_data_i,        // MPRF rs2 read data
    output  logic                               exu2mprf_w_req_o,           // MPRF write request
    output  logic [`SCR1_MPRF_AWIDTH-1:0]       exu2mprf_rd_addr_o,         // MPRF rd write address
    output  logic [`SCR1_XLEN-1:0]              exu2mprf_rd_data_o,         // MPRF rd write data

    // EXU <-> FPRF interface
	output  logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs1_addr_o,        // FPRF rs1 read address
    input   logic [`SCR1_XLEN-1:0]              fprf2exu_rs1_data_i,        // FPRF rs1 read data
    output  logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs2_addr_o,        // FPRF rs2 read address
    input   logic [`SCR1_XLEN-1:0]              fprf2exu_rs2_data_i,        // FPRF rs2 read data
    output  logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs3_addr_o,        // FPRF rs3 read address
    input   logic [`SCR1_XLEN-1:0]              fprf2exu_rs3_data_i,        // FPRF rs3 read data
    output  logic                               exu2fprf_w_req_o,           // FPRF write request
    output  logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rd_addr_o,         // FPRF rd write address
    output  logic [`SCR1_XLEN-1:0]              exu2fprf_rd_data_o,         // FPRF rd write data

    // EXU <-> CSR read/write interface
    output  logic [SCR1_CSR_ADDR_WIDTH-1:0]     exu2csr_rw_addr_o,          // CSR read/write address
    output  logic                               exu2csr_r_req_o,            // CSR read request
    input   logic [`SCR1_XLEN-1:0]              csr2exu_r_data_i,           // CSR read data
    output  logic                               exu2csr_w_req_o,            // CSR write request
    output  type_scr1_csr_cmd_sel_e             exu2csr_w_cmd_o,            // CSR write command
    output  logic [`SCR1_XLEN-1:0]              exu2csr_w_data_o,           // CSR write data
    input   logic                               csr2exu_rw_exc_i,           // CSR read/write access exception

    // EXU <-> CSR events interface
    output  logic                               exu2csr_take_irq_o,         // Take IRQ trap
    output  logic                               exu2csr_take_exc_o,         // Take exception trap
    output  logic                               exu2csr_mret_update_o,      // MRET update CSR
    output  logic                               exu2csr_mret_instr_o,       // MRET instruction
    output  logic                               exu2csr_sret_update_o,      // SRET update CSR
    output  logic                               exu2csr_sret_instr_o,       // SRET instruction
    output  type_scr1_exc_code_e                exu2csr_exc_code_o,         // Exception code (see scr1_arch_types.svh)
    output  logic [`SCR1_XLEN-1:0]              exu2csr_trap_val_o,         // Trap value
    input   logic [`SCR1_XLEN-1:0]              csr2exu_new_pc_i,           // Exception/IRQ/MRET new PC
    input   logic                               csr2exu_irq_i,              // IRQ request
    input   logic                               csr2exu_ip_ie_i,            // Some IRQ pending and locally enabled
    input   logic                               csr2exu_mstatus_mie_up_i,   // MSTATUS or MIE update in the current cycle
    input   logic                               csr2exu_sstatus_sie_up_i,   // SSTATUS or SIE update in the current cycle
	input	logic								csr2exu_trans_ldst_i,
	input	logic								csr2exu_tvm_i,				// CSR TVM enable
	input	logic								csr2exu_tsr_i,				// CSR SRET trap

    // EXU <-> DMEM interface
    output  logic                               exu2dmem_req_o,             // Data memory request
    output  type_scr1_mem_cmd_e                 exu2dmem_cmd_o,             // Data memory command
    output  type_scr1_mem_width_e               exu2dmem_width_o,           // Data memory width
    output  logic [`SCR1_XLEN-1:0]       		exu2dmem_addr_o,            // Data memory address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]       exu2dmem_wdata_o,           // Data memory write data
    input   logic                               dmem2exu_req_ack_i,         // Data memory request acknowledge
    input   logic [`SCR1_DMEM_DWIDTH-1:0]       dmem2exu_rdata_i,           // Data memory read data
    input   type_scr1_mem_resp_e                dmem2exu_resp_i,            // Data memory response

	// EXU <-> MMU interface
	output	logic								exu2mmu_lsu_req_o,
	output	logic [`SCR1_XLEN-1:0] 				exu2mmu_lsu_vaddr_o,  		// virtual address out
	output	type_scr1_lsu_cmd_sel_e				exu2mmu_lsu_cmd_o,
	output	logic [`SCR1_XLEN-1:0]				exu2mmu_vaddr_flush_o,
	output	logic [`SCR1_XLEN-1:0]				exu2mmu_asid_flush_o,

	input	logic 								mmu2lsu_dtlb_hit_i,  		// sent in same cycle as the request if translation hits in DTLB
	input	logic [44-1:0] 						mmu2lsu_dtlb_ppn_i,  		// ppn (send same cycle as hit)

	input	logic 								mmu2lsu_valid_i,  			// translation is valid
	input	logic [`SCR1_XLEN-1:0] 				mmu2lsu_paddr_i,  			// translated address
	input	logic 								mmu2lsu_exception_i,  		// address translation threw an exception
	input	type_scr1_exc_code_e				mmu2lsu_exc_code_i,  		// address translation threw an exception

	input	logic								mmu2lsu_req_i,
	input	type_scr1_lsu_cmd_sel_e				mmu2lsu_cmd_i,

	input	logic [`SCR1_XLEN-1:0]				mmu2lsu_addr_i,
	output	logic								lsu2mmu_rdy_o,
	output	logic [`SCR1_XLEN-1:0]				lsu2mmu_ldata_o,
	output	logic								lsu2mmu_exc_o,
	output	type_scr1_exc_code_e				lsu2mmu_exc_code_o,

	output	logic								exu2mmu_flush_tlb_o,

    // EXU control
    output  logic                               exu2pipe_exc_req_o,         // Exception on last instruction
    output  logic                               exu2pipe_brkpt_o,           // Software Breakpoint (EBREAK)
    output  logic                               exu2pipe_init_pc_o,         // Reset exit
    output  logic                               exu2pipe_wfi_run2halt_o,    // Transition to WFI halted state
    output  logic                               exu2pipe_instret_o,         // Instruction retired (with or without exception)
`ifndef SCR1_CSR_REDUCED_CNT
    output  logic                               exu2csr_instret_no_exc_o,   // Instruction retired (without exception)
`endif // SCR1_CSR_REDUCED_CNT
    output  logic                               exu2pipe_exu_busy_o,        // EXU busy

	// EXU control for FPU CSR
	input	logic [1:0]							csr2exu_mstatus_fs_i,
	output	logic								exu2csr_fpu_done_o,
	output	logic [4:0]							exu2csr_fpu_fflags_o,
	input	logic [2:0]							csr2exu_fpu_frm_i,


`ifdef SCR1_DBG_EN
    // EXU <-> HDU interface
    input   logic                               hdu2exu_no_commit_i,        // Forbid instruction commitment
    input   logic                               hdu2exu_irq_dsbl_i,         // Disable IRQ
    input   logic                               hdu2exu_pc_advmt_dsbl_i,    // Forbid PC advancement
    input   logic                               hdu2exu_dmode_sstep_en_i,   // Enable single-step
    input   logic                               hdu2exu_pbuf_fetch_i,       // Take instructions from Program Buffer
    input   logic                               hdu2exu_dbg_halted_i,       // Debug halted state
    input   logic                               hdu2exu_dbg_run2halt_i,     // Transition to debug halted state
    input   logic                               hdu2exu_dbg_halt2run_i,     // Transition to run state
    input   logic                               hdu2exu_dbg_run_start_i,    // First cycle of run state
    input   logic [`SCR1_XLEN-1:0]              hdu2exu_dbg_new_pc_i,       // New PC as starting point for HART Resume
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
    // EXU <-> TDU interface
    output type_scr1_brkm_instr_mon_s           exu2tdu_imon_o,             // Instruction monitor
    input  logic [SCR1_TDU_ALLTRIG_NUM-1:0]     tdu2exu_ibrkpt_match_i,     // Instruction breakpoint(s) match
    input  logic                                tdu2exu_ibrkpt_exc_req_i,   // Instruction breakpoint exception
    output type_scr1_brkm_lsu_mon_s             lsu2tdu_dmon_o,             // Data monitor
    input  logic                                tdu2lsu_ibrkpt_exc_req_i,   // Instruction breakpoint exception
    input  logic [SCR1_TDU_MTRIG_NUM-1:0]       tdu2lsu_dbrkpt_match_i,     // Data breakpoint(s) match
    input  logic                                tdu2lsu_dbrkpt_exc_req_i,   // Data breakpoint exception
    output logic [SCR1_TDU_ALLTRIG_NUM-1:0]     exu2tdu_ibrkpt_ret_o,       // Instruction with breakpoint flag retire
  `ifdef SCR1_DBG_EN
    output logic                                exu2hdu_ibrkpt_hw_o,        // Hardware breakpoint on current instruction
  `endif // SCR1_DBG_EN
`endif // SCR1_TDU_EN

    // PC interface
`ifdef SCR1_CLKCTRL_EN
    output  logic                               exu2pipe_wfi_halted_o,      // WFI halted state
`endif // SCR1_CLKCTRL_EN
    output  logic [`SCR1_XLEN-1:0]              exu2pipe_pc_curr_o,         // Current PC
    output  logic [`SCR1_XLEN-1:0]              exu2csr_pc_next_o,          // Next PC
    output  logic                               exu2ifu_pc_new_req_o,       // New PC request
    output  logic [`SCR1_XLEN-1:0]              exu2ifu_pc_new_o            // New PC data
);

//------------------------------------------------------------------------------
// Local parameters declaration
//------------------------------------------------------------------------------

localparam SCR1_JUMP_MASK = `SCR1_XLEN'hFFFF_FFFF_FFFF_FFFE;

//------------------------------------------------------------------------------
// Local types declaration
//------------------------------------------------------------------------------

typedef enum logic {
    SCR1_CSR_INIT,
    SCR1_CSR_RDY
} scr1_csr_access_e;

typedef enum logic [2:0] {
	SCR1_AMO_FSM_IDLE,
	SCR1_AMO_FSM_LOAD,
	SCR1_AMO_FSM_OP,
	SCR1_AMO_FSM_STORE,
	SCR1_AMO_FSM_FIN
} type_scr1_amo_fsm_e;

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// Instruction queue signals
//------------------------------------------------------------------------------
logic                               exu_queue_vd;
type_scr1_exu_cmd_s                 exu_queue;
logic                               exu_queue_barrier;

`ifdef SCR1_DBG_EN
logic                               dbg_run_start_npbuf;
`endif // SCR1_DBG_EN
logic                               exu_queue_en;
logic [`SCR1_XLEN-1:0]              exu_illegal_instr;

`ifndef SCR1_NO_EXE_STAGE
logic                               idu2exu_use_rs1_ff;
logic                               idu2exu_use_rs2_ff;
logic                               idu2exu_use_rs3_ff;

// EXU queue valid flag register signals
logic                               exu_queue_vd_upd;
logic                               exu_queue_vd_ff;
logic                               exu_queue_vd_next;
`endif // SCR1_NO_EXE_STAGE

// IALU signals
//------------------------------------------------------------------------------
`ifdef SCR1_RVM_EXT
logic                               ialu_rdy;
logic                               ialu_vd;
`endif // SCR1_RVM_EXT
logic [`SCR1_XLEN-1:0]              ialu_main_op1;
logic [`SCR1_XLEN-1:0]              ialu_main_op2;
logic [`SCR1_XLEN-1:0]              ialu_main_res;
logic [`SCR1_XLEN-1:0]              ialu_addr_op1;
logic [`SCR1_XLEN-1:0]              ialu_addr_op2;
logic [`SCR1_XLEN-1:0]              ialu_addr_res;
logic                               ialu_cmp;

// FPU signals
//------------------------------------------------------------------------------
logic [`SCR1_XLEN-1:0]				fpu_main_op1;
logic [`SCR1_XLEN-1:0]				fpu_main_op2;
logic [`SCR1_XLEN-1:0]				fpu_main_op3;
logic [`SCR1_XLEN-1:0]				fpu_int_op;

logic								fpu_vd;
logic								fpu_rdy;
logic [`SCR1_XLEN-1:0]				fpu_main_res;
logic [4:0]							fpu_status;


// FMV signals
//------------------------------------------------------------------------------
logic 								fmv_vd;
logic								fmv_x_to_w;
logic								fmv_w_to_x;
logic								fmv_x_to_d;
logic								fmv_d_to_x;

logic [`SCR1_XLEN-1:0]				fmv_result;

logic [`SCR1_XLEN-1:0]				fmv_int_to_fp;
logic [`SCR1_XLEN-1:0]				fmv_fp_to_int;

// AMO signals
//------------------------------------------------------------------------------
type_scr1_amo_fsm_e					amo_fsm_ff;
type_scr1_amo_fsm_e					amo_fsm_next;
logic								amo_fsm_idle;
logic								amo_fsm_load;
logic								amo_fsm_op;
logic								amo_fsm_store;
logic								amo_fsm_fin;

logic								amo_vd;
logic								amo_rdy;

logic								lsu_amo_req_load;
logic								lsu_amo_req_store;
type_scr1_lsu_cmd_sel_e				lsu_amo_cmd;

logic [`SCR1_XLEN-1:0]				lsu_amo_data_load;
logic [`SCR1_XLEN-1:0]				lsu_amo_data_store;

logic								ialu_amo_req;

logic								amo_sc_fail;

// Exceptions signals
//------------------------------------------------------------------------------
logic                               exu_exc_req;
`ifdef SCR1_DBG_EN
logic                               exu_exc_req_ff;
logic                               exu_exc_req_next;
`endif // SCR1_DBG_EN
type_scr1_exc_code_e                exc_code;
logic [`SCR1_XLEN-1:0]              exc_trap_val;

logic                               instr_fault_rvi_hi;
logic								mstatus_fs_exc;
logic								sfence_tvm;
logic								sret_tsr;

// WFI signals
//------------------------------------------------------------------------------
// WFI control signals
logic                               wfi_halt_cond;
logic                               wfi_run_req;
logic                               wfi_halt_req;

// WFI Run Start register
logic                               wfi_run_start_ff;
logic                               wfi_run_start_next;

// WFI halted register
logic                               wfi_halted_upd;
logic                               wfi_halted_ff;
logic                               wfi_halted_next;

// PC signals
//------------------------------------------------------------------------------
logic [3:0]                         init_pc_v;
logic                               init_pc;
logic [`SCR1_XLEN-1:0]              inc_pc;

logic                               branch_taken;
logic                               jb_taken;
logic [`SCR1_XLEN-1:0]              jb_new_pc;
logic                               jb_misalign;

// Current PC register
logic                               pc_curr_upd;
logic [`SCR1_XLEN-1:0]              pc_curr_ff;
logic [`SCR1_XLEN-1:0]              pc_curr_next;

// LSU signals
//------------------------------------------------------------------------------
logic                               lsu_req;
logic                               lsu_rdy;
logic [`SCR1_XLEN-1:0]              lsu_l_data;
logic                               lsu_exc_req;
type_scr1_exc_code_e                lsu_exc_code;

logic								lsu_req_trans;
logic								lsu_req_amo_load_trans;
logic								lsu_req_amo_store_trans;
logic [`SCR1_XLEN-1:0]				lsu_addr_trans;

// EXU status signals
//------------------------------------------------------------------------------
logic                               exu_rdy;

// MPRF signals
//------------------------------------------------------------------------------
logic                               mprf_rs1_req;
logic                               mprf_rs2_req;

logic   [`SCR1_MPRF_AWIDTH-1:0]     mprf_rs1_addr;
logic   [`SCR1_MPRF_AWIDTH-1:0]     mprf_rs2_addr;

// FPRF signals
//------------------------------------------------------------------------------
logic                               fprf_rs1_req;
logic                               fprf_rs2_req;
logic                               fprf_rs3_req;

logic   [`SCR1_MPRF_AWIDTH-1:0]     fprf_rs1_addr;
logic   [`SCR1_MPRF_AWIDTH-1:0]     fprf_rs2_addr;
logic   [`SCR1_MPRF_AWIDTH-1:0]     fprf_rs3_addr;

// CSR signals
//------------------------------------------------------------------------------
// CSR access register
scr1_csr_access_e                   csr_access_ff;
scr1_csr_access_e                   csr_access_next;
logic                               csr_access_init;

//------------------------------------------------------------------------------
// Instruction execution queue
//------------------------------------------------------------------------------
//
 // Instruction execution queue consists of the following functional units:
 // - EXU queue control logic
 // - EXU queue valid flag register
 // - EXU queue register
 // - EXU queue status logic
//

`ifdef SCR1_DBG_EN
assign dbg_run_start_npbuf = hdu2exu_dbg_run_start_i & ~hdu2exu_pbuf_fetch_i;
`endif // SCR1_DBG_EN

`ifndef SCR1_NO_EXE_STAGE

// EXU queue control logic
//------------------------------------------------------------------------------

assign exu_queue_barrier = wfi_halted_ff | wfi_halt_req | wfi_run_start_ff
`ifdef SCR1_DBG_EN
                         | hdu2exu_dbg_halted_i  | hdu2exu_dbg_run2halt_i
                         | dbg_run_start_npbuf
`endif // SCR1_DBG_EN
;

assign exu_queue_en = exu2idu_rdy_o & idu2exu_req_i;

// EXU queue valid flag register
//------------------------------------------------------------------------------

assign exu_queue_vd_upd = exu_queue_barrier | exu_rdy;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        exu_queue_vd_ff <= 1'b0;
    end else if (exu_queue_vd_upd) begin
        exu_queue_vd_ff <= exu_queue_vd_next;
    end
end

assign exu_queue_vd_next = ~exu_queue_barrier & idu2exu_req_i & ~exu2ifu_pc_new_req_o;
assign exu_queue_vd      = exu_queue_vd_ff;

// EXU queue register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (exu_queue_en) begin
        exu_queue.instr_rvc      <= idu2exu_cmd_i.instr_rvc;
		exu_queue.instr_rvf		 <= idu2exu_cmd_i.instr_rvf;
        exu_queue.ialu_op        <= idu2exu_cmd_i.ialu_op;
        exu_queue.ialu_cmd       <= idu2exu_cmd_i.ialu_cmd;
        exu_queue.sum2_op        <= idu2exu_cmd_i.sum2_op;
        exu_queue.lsu_cmd        <= idu2exu_cmd_i.lsu_cmd;
		exu_queue.fpu_cmd		 <= idu2exu_cmd_i.fpu_cmd;
		exu_queue.fpu_rnd		 <= idu2exu_cmd_i.fpu_rnd;
		exu_queue.fpu_src_fmt	 <= idu2exu_cmd_i.fpu_src_fmt;
		exu_queue.fpu_dst_fmt	 <= idu2exu_cmd_i.fpu_dst_fmt;
		exu_queue.fpu_int_fmt	 <= idu2exu_cmd_i.fpu_int_fmt;
		exu_queue.amo_cmd		 <= idu2exu_cmd_i.amo_cmd;
        exu_queue.csr_op         <= idu2exu_cmd_i.csr_op;
        exu_queue.csr_cmd        <= idu2exu_cmd_i.csr_cmd;
        exu_queue.rd_wb_sel      <= idu2exu_cmd_i.rd_wb_sel;
        exu_queue.rd_f_wb_sel    <= idu2exu_cmd_i.rd_f_wb_sel;
        exu_queue.jump_req       <= idu2exu_cmd_i.jump_req;
        exu_queue.branch_req     <= idu2exu_cmd_i.branch_req;
        exu_queue.mret_req       <= idu2exu_cmd_i.mret_req;
        exu_queue.sret_req       <= idu2exu_cmd_i.sret_req;
        exu_queue.fencei_req     <= idu2exu_cmd_i.fencei_req;
        exu_queue.wfi_req        <= idu2exu_cmd_i.wfi_req;
		exu_queue.sfence_req	 <= idu2exu_cmd_i.sfence_req;
        exu_queue.exc_req        <= idu2exu_cmd_i.exc_req;
        exu_queue.exc_code       <= idu2exu_cmd_i.exc_code;
        idu2exu_use_rs1_ff       <= idu2exu_use_rs1_i;
        idu2exu_use_rs2_ff       <= idu2exu_use_rs2_i;
        idu2exu_use_rs3_ff       <= idu2exu_use_rs3_i;
        if (idu2exu_use_rs1_i) begin
            exu_queue.rs1_addr   <= idu2exu_cmd_i.rs1_addr;
        end
        if (idu2exu_use_rs2_i) begin
            exu_queue.rs2_addr   <= idu2exu_cmd_i.rs2_addr;
        end
		if (idu2exu_use_rs3_i) begin
            exu_queue.rs3_addr   <= idu2exu_cmd_i.rs3_addr;
        end
        if (idu2exu_use_rd_i)  begin
            exu_queue.rd_addr    <= idu2exu_cmd_i.rd_addr;
        end
        if (idu2exu_use_imm_i) begin
            exu_queue.imm        <= idu2exu_cmd_i.imm;
        end
    end
end

`else // ~SCR1_NO_EXE_STAGE

assign exu_queue_barrier = wfi_halted_ff | wfi_run_start_ff
`ifdef SCR1_DBG_EN
                         | hdu2exu_dbg_halted_i  | dbg_run_start_npbuf
`endif // SCR1_DBG_EN
;
assign exu_queue_vd  = idu2exu_req_i & ~exu_queue_barrier;
assign exu_queue     = idu2exu_cmd_i;

`endif // ~SCR1_NO_EXE_STAGE

//------------------------------------------------------------------------------
// Integer Arithmetic Logic Unit (IALU)
//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Performs addition/subtraction and arithmetic and branch comparisons
 // - Performs logical operations (AND(I), OR(I), XOR(I))
 // - Performs address calculation for branch, jump, DMEM load and store and AUIPC
 //   instructions
 // - Performs shift operations
 // - Performs MUL/DIV operations
 //
//------------------------------------------------------------------------------

// IALU main operands fetch
//------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT
assign ialu_vd  = exu_queue_vd & (exu_queue.ialu_cmd != SCR1_IALU_CMD_NONE)
`ifdef SCR1_TDU_EN
                & ~tdu2exu_ibrkpt_exc_req_i
`endif // SCR1_TDU_EN
                ;
`endif // SCR1_RVM_EXT

always_comb begin
`ifdef SCR1_RVM_EXT
    if (~ialu_vd) begin
        ialu_main_op1 = '0;
        ialu_main_op2 = '0;
    end else begin
`endif // SCR1_RVM_EXT
        if (exu_queue.ialu_op == SCR1_IALU_OP_REG_REG) begin
            ialu_main_op1 = mprf2exu_rs1_data_i;
            ialu_main_op2 = mprf2exu_rs2_data_i;
		end else if (exu_queue.ialu_op == SCR1_IALU_OP_AMO_REG) begin
			ialu_main_op1 = lsu_amo_data_load;
			ialu_main_op2 = mprf2exu_rs2_data_i;
        end else begin
            ialu_main_op1 = mprf2exu_rs1_data_i;
            ialu_main_op2 = exu_queue.imm;
        end
`ifdef SCR1_RVM_EXT
    end
`endif // SCR1_RVM_EXT
end

// IALU address operands fetch
//------------------------------------------------------------------------------

always_comb begin
    if (exu_queue.sum2_op == SCR1_SUM2_OP_REG_IMM) begin
        ialu_addr_op1 = mprf2exu_rs1_data_i;
        ialu_addr_op2 = exu_queue.imm;
    end else begin
        ialu_addr_op1 = pc_curr_ff;
        ialu_addr_op2 = exu_queue.imm;
    end
end

// IALU module instantiation
//------------------------------------------------------------------------------

scr1_pipe_ialu i_ialu(
`ifdef SCR1_RVM_EXT
    // Common
    .clk                        (clk               ),
    .rst_n                      (rst_n             ),
    .exu2ialu_rvm_cmd_vd_i      (ialu_vd           ),
    .ialu2exu_rvm_res_rdy_o     (ialu_rdy          ),
`endif // SCR1_RVM_EXT

    // IALU
    .exu2ialu_main_op1_i        (ialu_main_op1     ),
    .exu2ialu_main_op2_i        (ialu_main_op2     ),
    .exu2ialu_cmd_i             (exu_queue.ialu_cmd),
    .ialu2exu_main_res_o        (ialu_main_res     ),
    .ialu2exu_cmp_res_o         (ialu_cmp          ),

    // Address adder signals
    .exu2ialu_addr_op1_i        (ialu_addr_op1     ),
    .exu2ialu_addr_op2_i        (ialu_addr_op2     ),
    .ialu2exu_addr_res_o        (ialu_addr_res     )
);

//------------------------------------------------------------------------------
// Floating-Point arithmetic Unit (FPU)
//------------------------------------------------------------------------------

// FPU main operands fetch
//------------------------------------------------------------------------------

assign fpu_vd  		= exu_queue_vd 
					& (exu_queue.fpu_cmd != SCR1_FPU_CMD_NONE)
					& (exu_queue.fpu_cmd != SCR1_FPU_CMD_FMV)
`ifdef SCR1_TDU_EN
                	& ~tdu2exu_ibrkpt_exc_req_i
`endif // SCR1_TDU_EN
;

assign fpu_main_op1 = fprf2exu_rs1_data_i;
assign fpu_main_op2 = fprf2exu_rs2_data_i;
assign fpu_main_op3 = fprf2exu_rs3_data_i;
assign fpu_int_op	= mprf2exu_rs1_data_i;


// FPU module instantiation
//------------------------------------------------------------------------------

scr1_pipe_fpu i_fpu (
	.clk					(clk					),
	.rst_n					(rst_n					),
	
	.exu2fpu_main_op1_i		(fpu_main_op1			),
	.exu2fpu_main_op2_i		(fpu_main_op2			),
	.exu2fpu_main_op3_i		(fpu_main_op3			),
	.exu2fpu_int_op_i		(fpu_int_op				),
	
	.exu2fpu_cmd_i			(exu_queue.fpu_cmd		),
	.exu2fpu_rnd_i			(exu_queue.fpu_rnd		),
	.exu2fpu_frm_i			(csr2exu_fpu_frm_i		),

	.exu2fpu_src_fmt_i		(exu_queue.fpu_src_fmt	),
	.exu2fpu_dst_fmt_i		(exu_queue.fpu_dst_fmt	),
	.exu2fpu_int_fmt_i		(exu_queue.fpu_int_fmt	),
	
	.exu2fpu_valid_i		(fpu_vd					),
	.fpu2exu_ready_o		(fpu_rdy				),
	.fpu2exu_result_o		(fpu_main_res			),
	.fpu2exu_status_o		(fpu_status				)
);


// FPU module instantiation
//------------------------------------------------------------------------------

assign	fmv_vd			= (exu_queue.fpu_cmd == SCR1_FPU_CMD_FMV);

assign	fmv_x_to_w		= (fmv_vd 
						& (exu_queue.fpu_src_fmt == SCR1_FPU_FMT_F32) 
						& (exu_queue.fpu_dst_fmt == SCR1_FPU_FMT_F32));
assign	fmv_w_to_x		= (fmv_vd 
						& (exu_queue.fpu_src_fmt == SCR1_FPU_FMT_F64) 
						& (exu_queue.fpu_dst_fmt == SCR1_FPU_FMT_F32));
assign	fmv_x_to_d		= (fmv_vd 
						& (exu_queue.fpu_src_fmt == SCR1_FPU_FMT_F32) 
						& (exu_queue.fpu_dst_fmt == SCR1_FPU_FMT_F64));
assign	fmv_d_to_x		= (fmv_vd 
						& (exu_queue.fpu_src_fmt == SCR1_FPU_FMT_F64) 
						& (exu_queue.fpu_dst_fmt == SCR1_FPU_FMT_F64));

always_comb begin
	case (1'b1)
		fmv_w_to_x	: fmv_int_to_fp = {{32{1'b1}}, fpu_int_op[31:0]};
		fmv_d_to_x	: fmv_int_to_fp = fpu_int_op;
		default		: fmv_int_to_fp = 64'd0;
	endcase
end

always_comb begin
	case (1'b1)
		fmv_x_to_w	: fmv_fp_to_int = {{32{fpu_main_op1[31]}}, fpu_main_op1[31:0]};
		fmv_x_to_d	: fmv_fp_to_int = fpu_main_op1;
		default		: fmv_fp_to_int = 64'd0;
	endcase
end


//------------------------------------------------------------------------------
// Atomic Memory Operation (AMO)
//------------------------------------------------------------------------------

assign amo_vd 	= exu_queue_vd & (exu_queue.amo_cmd != SCR1_AMO_CMD_NONE);

// FSM
always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		amo_fsm_ff	<= SCR1_AMO_FSM_IDLE;
	end
	else begin
		amo_fsm_ff	<= amo_fsm_next;
	end
end

always_comb begin
	case (1'b1)
		(amo_fsm_idle	& amo_vd)		: amo_fsm_next = SCR1_AMO_FSM_LOAD;
		(amo_fsm_load	& lsu_rdy)		: amo_fsm_next = SCR1_AMO_FSM_OP;
		(amo_fsm_op		& amo_sc_fail)	: amo_fsm_next = SCR1_AMO_FSM_FIN;
		(amo_fsm_op 	& ialu_rdy)		: amo_fsm_next = SCR1_AMO_FSM_STORE;
		(amo_fsm_store	& lsu_rdy)		: amo_fsm_next = SCR1_AMO_FSM_FIN;
		(amo_fsm_fin)					: amo_fsm_next = SCR1_AMO_FSM_IDLE;
		default							: amo_fsm_next = amo_fsm_ff;
	endcase
end

assign amo_fsm_idle		= (amo_fsm_ff == SCR1_AMO_FSM_IDLE);
assign amo_fsm_load		= (amo_fsm_ff == SCR1_AMO_FSM_LOAD);
assign amo_fsm_op		= (amo_fsm_ff == SCR1_AMO_FSM_OP);
assign amo_fsm_store	= (amo_fsm_ff == SCR1_AMO_FSM_STORE);
assign amo_fsm_fin		= (amo_fsm_ff == SCR1_AMO_FSM_FIN);

assign amo_sc_fail		= (amo_fsm_op
						& ((exu_queue.ialu_cmd == SCR1_IALU_CMD_SC) | (exu_queue.ialu_cmd == SCR1_IALU_CMD_SCW))
						& (ialu_main_res == `SCR1_XLEN'd1));

assign amo_rdy			= amo_fsm_fin;

// control signals
assign lsu_amo_req_load		= exu_queue_vd & (amo_fsm_ff == SCR1_AMO_FSM_LOAD);
assign ialu_amo_req			= exu_queue_vd & (amo_fsm_ff == SCR1_AMO_FSM_OP);
assign lsu_amo_req_store	= exu_queue_vd & (amo_fsm_ff == SCR1_AMO_FSM_STORE);

// AMO LSU CMD
always_comb begin
	case (1'b1)
		(amo_fsm_load & (exu_queue.amo_cmd == SCR1_AMO_CMD_WORD))	: lsu_amo_cmd = SCR1_LSU_CMD_LW;
		(amo_fsm_store & (exu_queue.amo_cmd == SCR1_AMO_CMD_WORD))	: lsu_amo_cmd = SCR1_LSU_CMD_SW;
		(amo_fsm_load & (exu_queue.amo_cmd == SCR1_AMO_CMD_DWORD)) 	: lsu_amo_cmd = SCR1_LSU_CMD_LD;
		(amo_fsm_store & (exu_queue.amo_cmd == SCR1_AMO_CMD_DWORD))	: lsu_amo_cmd = SCR1_LSU_CMD_SD;
		default														: lsu_amo_cmd = SCR1_LSU_CMD_NONE;	
	endcase
end

// loaded data
always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		lsu_amo_data_load	<= '0;
	end
	else if (amo_fsm_load) begin
		lsu_amo_data_load	<= lsu_l_data;
	end
end

// data to be stored
assign lsu_amo_data_store	= ((exu_queue.ialu_cmd == SCR1_IALU_CMD_SC) | (exu_queue.ialu_cmd == SCR1_IALU_CMD_SCW)) ?	mprf2exu_rs2_data_i
							: ((exu_queue.ialu_cmd == SCR1_IALU_CMD_LR) | (exu_queue.ialu_cmd == SCR1_IALU_CMD_LRW)) ?	lsu_amo_data_load

							: ialu_main_res;


//------------------------------------------------------------------------------
// Exceptions logic
//------------------------------------------------------------------------------
//
 // Exceptions logic consists of the following functional units:
 // - Exception request logic
 // - Exception code encoder
 // - Exception trap value multiplexer
 //
//

`ifndef SCR1_RVC_EXT
assign jb_misalign  = exu_queue_vd  & jb_taken & |jb_new_pc[1:0];
`else
assign jb_misalign	= exu_queue_vd  & jb_taken & jb_new_pc[0];
`endif // ~SCR1_RVC_EXT

assign mstatus_fs_exc	= (exu_queue.instr_rvf & (csr2exu_mstatus_fs_i == 2'b00));
assign sfence_tvm		= csr2exu_tvm_i & exu_queue.sfence_req;
assign sret_tsr			= csr2exu_tsr_i & exu_queue.sret_req;

// Exception request
assign exu_exc_req  = exu_queue_vd & (exu_queue.exc_req | lsu_exc_req
                                                        | csr2exu_rw_exc_i
`ifndef SCR1_RVC_EXT
                                                        | jb_misalign
`endif // ~SCR1_RVC_EXT
`ifdef SCR1_TDU_EN
  `ifdef SCR1_DBG_EN
                                                        | exu2hdu_ibrkpt_hw_o
  `endif // SCR1_DBG_EN
`endif // SCR1_TDU_EN
														| mstatus_fs_exc
														| sfence_tvm
														| sret_tsr
                                                        );

// EXU exception request register
//------------------------------------------------------------------------------

`ifdef SCR1_DBG_EN

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        exu_exc_req_ff <= 1'b0;
    end else begin
        exu_exc_req_ff <= exu_exc_req_next;
    end
end

assign exu_exc_req_next = hdu2exu_dbg_halt2run_i ? 1'b0 : exu_exc_req;
`endif // SCR1_DBG_EN

// Exception code encoder
//------------------------------------------------------------------------------

always_comb begin
    case (1'b1)
`ifdef SCR1_TDU_EN
  `ifdef SCR1_DBG_EN
        exu2hdu_ibrkpt_hw_o: exc_code = SCR1_EXC_CODE_BREAKPOINT;
  `endif // SCR1_DBG_EN
`endif // SCR1_TDU_EN
        exu_queue.exc_req  : exc_code = exu_queue.exc_code;
`ifndef SCR1_RVC_EXT
        jb_misalign        : exc_code = SCR1_EXC_CODE_INSTR_MISALIGN;
`endif // ~SCR1_RVC_EXT
        lsu_exc_req        : exc_code = lsu_exc_code;
        csr2exu_rw_exc_i   : exc_code = SCR1_EXC_CODE_ILLEGAL_INSTR;
		mstatus_fs_exc	   : exc_code = SCR1_EXC_CODE_ILLEGAL_INSTR;
		sfence_tvm		   : exc_code = SCR1_EXC_CODE_ILLEGAL_INSTR;
		sret_tsr		   : exc_code = SCR1_EXC_CODE_ILLEGAL_INSTR;
        default            : exc_code = SCR1_EXC_CODE_ECALL_M;
    endcase // 1'b1
end

// Exception trap value multiplexer
//------------------------------------------------------------------------------

assign instr_fault_rvi_hi = exu_queue.instr_rvc;
assign exu_illegal_instr = {exu2csr_rw_addr_o,          // CSR address
                            5'(exu_queue.rs1_addr),     // rs1 / zimm
                            exu_queue.imm[14:12],       // funct3
                            5'(exu_queue.rd_addr),      // rd
                            SCR1_OPCODE_SYSTEM,
                            SCR1_INSTR_RVI
                           };

// If Instruction Access Fault occurred on high part of RVI instruction trap
// value is set to point on the high part of the instruction (inc_pc=pc+2)
always_comb begin
    case (exc_code)
`ifndef SCR1_RVC_EXT
        SCR1_EXC_CODE_INSTR_MISALIGN    : exc_trap_val = jb_new_pc;
`endif // SCR1_RVC_EXT
        SCR1_EXC_CODE_INSTR_ACCESS_FAULT: exc_trap_val = instr_fault_rvi_hi
                                                       ? inc_pc
                                                       : pc_curr_ff;
`ifdef SCR1_MTVAL_ILLEGAL_INSTR_EN
        SCR1_EXC_CODE_ILLEGAL_INSTR     : exc_trap_val = exu_queue.exc_req
                                                       ? exu_queue.imm
                                                       : exu_illegal_instr;
`else // SCR1_MTVAL_ILLEGAL_INSTR_EN
        SCR1_EXC_CODE_ILLEGAL_INSTR     : exc_trap_val = '0;
`endif // SCR1_MTVAL_ILLEGAL_INSTR_EN
`ifdef SCR1_TDU_EN
        SCR1_EXC_CODE_BREAKPOINT: begin
            case (1'b1)
                tdu2exu_ibrkpt_exc_req_i: exc_trap_val = pc_curr_ff;
                tdu2lsu_dbrkpt_exc_req_i: exc_trap_val = ialu_addr_res;
                default                 : exc_trap_val = '0;
            endcase
        end
`endif // SCR1_TDU_EN
        SCR1_EXC_CODE_LD_ADDR_MISALIGN,
        SCR1_EXC_CODE_LD_ACCESS_FAULT,
        SCR1_EXC_CODE_ST_ADDR_MISALIGN,
        SCR1_EXC_CODE_ST_ACCESS_FAULT   : exc_trap_val = ialu_addr_res;
        default                         : exc_trap_val = '0;
    endcase // exc_code
end

//------------------------------------------------------------------------------
// WFI logic
//------------------------------------------------------------------------------
//
 // Wait for interrupt (WFI) logic consists of the following functional units:
 // - WFI control logic
 // - WFI Run Start register
 // - WFI Halted flag register
 // - WFI status signals
//

// WFI control logic
//------------------------------------------------------------------------------

assign wfi_halt_cond = ~csr2exu_ip_ie_i
                     & ((exu_queue_vd & exu_queue.wfi_req) | wfi_run_start_ff)
`ifdef SCR1_DBG_EN
                     & ~hdu2exu_no_commit_i & ~hdu2exu_dmode_sstep_en_i & ~hdu2exu_dbg_run2halt_i
`endif // SCR1_DBG_EN
                     ;
assign wfi_halt_req  = ~wfi_halted_ff & wfi_halt_cond;

// HART will exit WFI halted state if the event that causes the HART to resume
// execution occurs even if it doesn't cause an interrupt to be taken
assign wfi_run_req   = wfi_halted_ff  & (csr2exu_ip_ie_i
`ifdef SCR1_DBG_EN
                                      | hdu2exu_dbg_halt2run_i
`endif // SCR1_DBG_EN
                                      );

// WFI Run Start register
//------------------------------------------------------------------------------

`ifndef SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk) begin
`else // SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk_alw_on) begin
`endif // SCR1_CLKCTRL_EN
    if (~rst_n) begin
        wfi_run_start_ff <= 1'b0;
    end else begin
        wfi_run_start_ff <= wfi_run_start_next;
    end
end

assign wfi_run_start_next = wfi_halted_ff & csr2exu_ip_ie_i & ~exu2csr_take_irq_o;

// WFI halted flag register
//------------------------------------------------------------------------------

assign wfi_halted_upd = wfi_halt_req | wfi_run_req;

`ifndef SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk) begin
`else // SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk_alw_on) begin
`endif // SCR1_CLKCTRL_EN
    if (~rst_n) begin
        wfi_halted_ff <= 1'b0;
    end else if (wfi_halted_upd) begin
        wfi_halted_ff <= wfi_halted_next;
    end
end

assign wfi_halted_next = wfi_halt_req | ~wfi_run_req;

// WFI status signals
//------------------------------------------------------------------------------

assign exu2pipe_wfi_run2halt_o = wfi_halt_req;
`ifdef SCR1_CLKCTRL_EN
assign exu2pipe_wfi_halted_o   = wfi_halted_ff;
`endif // SCR1_CLKCTRL_EN

//------------------------------------------------------------------------------
// Program Counter logic
//------------------------------------------------------------------------------
//
 // PC logic consists of the following functional units:
 // - PC initialization logic
 // - Current PC register
 // - New PC multiplexer

// PC initialization logic
//------------------------------------------------------------------------------
// Generates a New PC request to set PC to reset value

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        init_pc_v <= '0;
    end else begin
        if (~&init_pc_v) begin
            init_pc_v <= {init_pc_v[2:0], 1'b1};
        end
    end
end

assign init_pc = ~init_pc_v[3] & init_pc_v[2];

// Current PC register
//------------------------------------------------------------------------------

assign pc_curr_upd = ((exu2pipe_instret_o | exu2csr_take_irq_o
`ifdef SCR1_DBG_EN
                   | dbg_run_start_npbuf) & ( ~hdu2exu_pc_advmt_dsbl_i
                                            & ~hdu2exu_no_commit_i
`endif // SCR1_DBG_EN
                   ));

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        pc_curr_ff <= SCR1_RST_VECTOR;
    end else if (pc_curr_upd) begin
        pc_curr_ff <= pc_curr_next;
    end
end

`ifdef SCR1_RVC_EXT
assign inc_pc = pc_curr_ff + (exu_queue.instr_rvc ? `SCR1_XLEN'd2 : `SCR1_XLEN'd4);
`else // ~SCR1_RVC_EXT
assign inc_pc = pc_curr_ff + `SCR1_XLEN'd4;
`endif // ~SCR1_RVC_EXT

assign pc_curr_next = exu2ifu_pc_new_req_o        ? exu2ifu_pc_new_o
                    : (inc_pc[6] ^ pc_curr_ff[6]) ? inc_pc
                                                  : {pc_curr_ff[`SCR1_XLEN-1:6], inc_pc[5:0]};

// New PC multiplexer
//------------------------------------------------------------------------------

always_comb begin
    case (1'b1)
        init_pc             : exu2ifu_pc_new_o = SCR1_RST_VECTOR;
        exu2csr_take_exc_o,
        exu2csr_take_irq_o,
        exu2csr_mret_instr_o,
		exu2csr_sret_instr_o: exu2ifu_pc_new_o = csr2exu_new_pc_i;
`ifdef SCR1_DBG_EN
        dbg_run_start_npbuf : exu2ifu_pc_new_o = hdu2exu_dbg_new_pc_i;
`endif // SCR1_DBG_EN
        wfi_run_start_ff    : exu2ifu_pc_new_o = pc_curr_ff;
        exu_queue.fencei_req: exu2ifu_pc_new_o = inc_pc;
        exu_queue.sfence_req: exu2ifu_pc_new_o = inc_pc;
        default             : exu2ifu_pc_new_o = ialu_addr_res & SCR1_JUMP_MASK;
    endcase
end

assign exu2ifu_pc_new_req_o = init_pc                                        // reset
                            | exu2csr_take_irq_o
                            | exu2csr_take_exc_o
                            | (exu2csr_mret_instr_o & ~csr2exu_mstatus_mie_up_i)
                            | (exu2csr_sret_instr_o & ~csr2exu_sstatus_sie_up_i)
                            | (exu_queue_vd & exu_queue.fencei_req)
							| (exu_queue_vd & exu_queue.sfence_req)
                            | (wfi_run_start_ff
`ifdef SCR1_CLKCTRL_EN
                            & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                            )
`ifdef SCR1_DBG_EN
                            | dbg_run_start_npbuf
`endif // SCR1_DBG_EN
                            | (exu_queue_vd & jb_taken);

// Jump/branch signals
assign branch_taken = exu_queue.branch_req & ialu_cmp;
assign jb_taken     = exu_queue.jump_req | branch_taken;
assign jb_new_pc    = ialu_addr_res & SCR1_JUMP_MASK;

// PC to be loaded on MRET from interrupt trap
assign exu2csr_pc_next_o  = ~exu_queue_vd ? pc_curr_ff
                          : jb_taken      ? jb_new_pc
                                          : inc_pc;
assign exu2pipe_pc_curr_o = pc_curr_ff;

//------------------------------------------------------------------------------
// Load/Store Unit (LSU)
//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Performs load and store operations in Data Memory
 // - Generates DMEM address misalign and access fault exceptions
 // - Passes DMEM operations information to TDU and generates LSU breakpoint exception
 //
//------------------------------------------------------------------------------

assign lsu_req  = ((exu_queue.lsu_cmd != SCR1_LSU_CMD_NONE) & exu_queue_vd & ~mstatus_fs_exc);

scr1_pipe_lsu i_lsu(
    .rst_n                      (rst_n                   ),
    .clk                        (clk                     ),

    // EXU <-> LSU interface
    .exu2lsu_req_i              (lsu_req_trans           ),       // Request to LSU
    .exu2lsu_cmd_i              (exu_queue.lsu_cmd       ),       // LSU command
    .exu2lsu_addr_i             (lsu_addr_trans          ),       // DMEM address
    .exu2lsu_sdata_i            (mprf2exu_rs2_data_i     ),       // Data for store (INT) to DMEM
    .exu2lsu_fsdata_i           (fprf2exu_rs2_data_i     ),       // Data for store (FP) to DMEM
    .lsu2exu_rdy_o              (lsu_rdy                 ),       // LSU ready
    .lsu2exu_ldata_o            (lsu_l_data              ),       // Loaded data form DMEM
    .lsu2exu_exc_o              (lsu_exc_req             ),       // LSU exception
    .lsu2exu_exc_code_o         (lsu_exc_code            ),       // LSU exception code

	.exu2lsu_amo_req_load_i		(lsu_amo_req_load		),
	.exu2lsu_amo_req_store_i	(lsu_amo_req_store		),
	.exu2lsu_amo_cmd_i			(lsu_amo_cmd			),
	.exu2lsu_amo_sdata_i		(lsu_amo_data_store		),

	.mmu2lsu_exc_i				(mmu2lsu_exception_i	),
	.mmu2lsu_exc_code_i			(mmu2lsu_exc_code_i		),

`ifdef SCR1_TDU_EN
    // TDU <-> LSU interface
    .lsu2tdu_dmon_o             (lsu2tdu_dmon_o          ),
    .tdu2lsu_ibrkpt_exc_req_i   (tdu2lsu_ibrkpt_exc_req_i),
    .tdu2lsu_dbrkpt_exc_req_i   (tdu2lsu_dbrkpt_exc_req_i),
`endif // SCR1_TDU_EN

    // Data memory interface
    .lsu2dmem_req_o             (exu2dmem_req_o          ),       // DMEM request
    .lsu2dmem_cmd_o             (exu2dmem_cmd_o          ),       // DMEM command
    .lsu2dmem_width_o           (exu2dmem_width_o        ),       // DMEM width
    .lsu2dmem_addr_o            (exu2dmem_addr_o         ),       // DMEM address
    .lsu2dmem_wdata_o           (exu2dmem_wdata_o        ),       // DMEM write data
    .dmem2lsu_req_ack_i         (dmem2exu_req_ack_i      ),       // DMEM request acknowledge
    .dmem2lsu_rdata_i           (dmem2exu_rdata_i        ),       // DMEM read data
    .dmem2lsu_resp_i            (dmem2exu_resp_i         )        // DMEM response
);

assign exu2mmu_lsu_req_o		= lsu_req | lsu_amo_req_load | lsu_amo_req_store;
assign exu2mmu_lsu_vaddr_o		= ialu_addr_res;
assign exu2mmu_lsu_cmd_o		= exu_queue.lsu_cmd;

assign exu2mmu_vaddr_flush_o	= mprf2exu_rs1_data_i;
assign exu2mmu_asid_flush_o		= mprf2exu_rs2_data_i;

assign lsu_req_trans			= (csr2exu_trans_ldst_i)	? mmu2lsu_valid_i & lsu_req
								: lsu_req;
assign lsu_req_amo_load_trans	= (csr2exu_trans_ldst_i)	? mmu2lsu_valid_i & lsu_amo_req_load
								: lsu_amo_req_load;
assign lsu_req_amo_store_trans	= (csr2exu_trans_ldst_i)	? mmu2lsu_valid_i & lsu_amo_req_store
								: lsu_amo_req_store;
assign lsu_addr_trans			= (csr2exu_trans_ldst_i)	? mmu2lsu_paddr_i
								: ialu_addr_res;

assign exu2mmu_flush_tlb_o		= exu_queue.sfence_req;

//------------------------------------------------------------------------------
// EXU status logic
//------------------------------------------------------------------------------

// EXU ready flag
always_comb begin
    case (1'b1)
        lsu_req                 : exu_rdy = lsu_rdy | lsu_exc_req;
		amo_vd					: exu_rdy = amo_rdy;
`ifdef SCR1_RVM_EXT
        ialu_vd                 : exu_rdy = ialu_rdy;
`endif // SCR1_RVM_EXT
		fpu_vd					: exu_rdy = fpu_rdy;
		fmv_vd					: exu_rdy = 1'b1;
        csr2exu_mstatus_mie_up_i: exu_rdy = 1'b0;
        csr2exu_sstatus_sie_up_i: exu_rdy = 1'b0;
        default                 : exu_rdy = 1'b1;
    endcase
end

assign exu2pipe_init_pc_o       = init_pc;
assign exu2idu_rdy_o            = exu_rdy & ~exu_queue_barrier;
assign exu2pipe_exu_busy_o      = exu_queue_vd & ~exu_rdy;
assign exu2pipe_instret_o       = exu_queue_vd & exu_rdy;
`ifndef SCR1_CSR_REDUCED_CNT
assign exu2csr_instret_no_exc_o = exu2pipe_instret_o & ~exu_exc_req;
`endif // SCR1_CSR_REDUCED_CNT

assign exu2csr_fpu_done_o		= exu_queue_vd & fpu_rdy;
assign exu2csr_fpu_fflags_o		= fpu_status;

// Exceptions
`ifdef SCR1_DBG_EN
assign exu2pipe_exc_req_o  = exu_queue_vd ? exu_exc_req : exu_exc_req_ff;
`else // SCR1_DBG_EN
assign exu2pipe_exc_req_o  = exu_exc_req;
`endif // SCR1_DBG_EN

// Breakpoints
assign exu2pipe_brkpt_o    = exu_queue_vd & (exu_queue.exc_code == SCR1_EXC_CODE_BREAKPOINT);
`ifdef SCR1_TDU_EN
  `ifdef SCR1_DBG_EN
assign exu2hdu_ibrkpt_hw_o = tdu2exu_ibrkpt_exc_req_i | tdu2lsu_dbrkpt_exc_req_i;
  `endif // SCR1_DBG_EN
`endif // SCR1_TDU_EN

//------------------------------------------------------------------------------
// EXU <-> MPRF interface
//------------------------------------------------------------------------------

// Operands fetching stage
//------------------------------------------------------------------------------

`ifdef  SCR1_NO_EXE_STAGE
assign mprf_rs1_req = exu_queue_vd & idu2exu_use_rs1_i;
assign mprf_rs2_req = exu_queue_vd & idu2exu_use_rs2_i;
`else // SCR1_NO_EXE_STAGE
assign mprf_rs1_req = exu_queue_vd & idu2exu_use_rs1_ff;
assign mprf_rs2_req = exu_queue_vd & idu2exu_use_rs2_ff;
`endif // SCR1_NO_EXE_STAGE

assign mprf_rs1_addr = exu_queue.rs1_addr[`SCR1_MPRF_AWIDTH-1:0];
assign mprf_rs2_addr = exu_queue.rs2_addr[`SCR1_MPRF_AWIDTH-1:0];

assign exu2mprf_rs1_addr_o = mprf_rs1_req ? mprf_rs1_addr[`SCR1_MPRF_AWIDTH-1:0] : '0;
assign exu2mprf_rs2_addr_o = mprf_rs2_req ? mprf_rs2_addr[`SCR1_MPRF_AWIDTH-1:0] : '0;


//------------------------------------------------------------------------------
// EXU <-> FPRF interface
//------------------------------------------------------------------------------

// Operands fetching stage
//------------------------------------------------------------------------------

`ifdef  SCR1_NO_EXE_STAGE
assign fprf_rs1_req = exu_queue_vd & idu2exu_use_rs1_i;
assign fprf_rs2_req = exu_queue_vd & idu2exu_use_rs2_i;
assign fprf_rs3_req = exu_queue_vd & idu2exu_use_rs3_i;
`else // SCR1_NO_EXE_STAGE
assign fprf_rs1_req = exu_queue_vd & idu2exu_use_rs1_ff;
assign fprf_rs2_req = exu_queue_vd & idu2exu_use_rs2_ff;
assign fprf_rs3_req = exu_queue_vd & idu2exu_use_rs3_ff;
`endif // SCR1_NO_EXE_STAGE

assign fprf_rs1_addr = exu_queue.rs1_addr[`SCR1_MPRF_AWIDTH-1:0];
assign fprf_rs2_addr = exu_queue.rs2_addr[`SCR1_MPRF_AWIDTH-1:0];
assign fprf_rs3_addr = exu_queue.rs3_addr[`SCR1_MPRF_AWIDTH-1:0];

assign exu2fprf_rs1_addr_o = fprf_rs1_req ? fprf_rs1_addr[`SCR1_MPRF_AWIDTH-1:0] : '0;
assign exu2fprf_rs2_addr_o = fprf_rs2_req ? fprf_rs2_addr[`SCR1_MPRF_AWIDTH-1:0] : '0;
assign exu2fprf_rs3_addr_o = fprf_rs3_req ? fprf_rs3_addr[`SCR1_MPRF_AWIDTH-1:0] : '0;


// Write back stage
//------------------------------------------------------------------------------

assign exu2mprf_w_req_o   = (exu_queue.rd_wb_sel != SCR1_RD_WB_NONE) & exu_queue_vd & ~exu_exc_req
`ifdef SCR1_DBG_EN
                          & ~hdu2exu_no_commit_i
`endif // SCR1_DBG_EN
                          & ((exu_queue.rd_wb_sel == SCR1_RD_WB_CSR) ? csr_access_init : exu_rdy);

assign exu2mprf_rd_addr_o = `SCR1_MPRF_AWIDTH'(exu_queue.rd_addr);

// MRPF RD data multiplexer
always_comb begin
    case (exu_queue.rd_wb_sel)
        SCR1_RD_WB_SUM2  	: exu2mprf_rd_data_o = ialu_addr_res;
        SCR1_RD_WB_IMM   	: exu2mprf_rd_data_o = exu_queue.imm;
        SCR1_RD_WB_INC_PC	: exu2mprf_rd_data_o = inc_pc;
        SCR1_RD_WB_LSU   	: exu2mprf_rd_data_o = lsu_l_data;
		SCR1_RD_WB_FPU	 	: exu2mprf_rd_data_o = fpu_main_res;
		SCR1_RD_WB_FMV		: exu2mprf_rd_data_o = fmv_fp_to_int;
		SCR1_RD_WB_AMO		: exu2mprf_rd_data_o = lsu_amo_data_load;
        SCR1_RD_WB_CSR   	: exu2mprf_rd_data_o = csr2exu_r_data_i;
        default          	: exu2mprf_rd_data_o = ialu_main_res;
    endcase
end


assign exu2fprf_w_req_o   = (exu_queue.rd_f_wb_sel != SCR1_RD_F_WB_NONE) & exu_queue_vd & ~exu_exc_req
`ifdef SCR1_DBG_EN
                          & ~hdu2exu_no_commit_i
`endif // SCR1_DBG_EN
                          & ((exu_queue.rd_f_wb_sel == SCR1_RD_F_WB_CSR) ? csr_access_init : exu_rdy);

assign exu2fprf_rd_addr_o = `SCR1_FPRF_AWIDTH'(exu_queue.rd_addr);

// FPRF RD data multiplexer
always_comb begin
	case (exu_queue.rd_f_wb_sel)
		SCR1_RD_F_WB_FPU	: exu2fprf_rd_data_o = fpu_main_res;
		SCR1_RD_F_WB_LSU	: exu2fprf_rd_data_o = lsu_l_data;
		SCR1_RD_F_WB_FMV	: exu2fprf_rd_data_o = fmv_int_to_fp;
		SCR1_RD_F_WB_CSR	: exu2fprf_rd_data_o = csr2exu_r_data_i;
		default				: exu2fprf_rd_data_o = fpu_main_res;
	endcase
end

//------------------------------------------------------------------------------
// EXU <-> CSR interface
//------------------------------------------------------------------------------
//
 // EXU <-> CSR interface consists of the following functional units:
 // - CSR write/read interface
 // - CSR access FSM
 // - CSR events interface:
 //   - Exceptions signals
 //   - Interrupts signals
 //   - MRET signals
//

// CSRs write/read interface
//------------------------------------------------------------------------------

// CSR write/read request signals calculation
always_comb begin
    if (~exu_queue_vd
`ifdef SCR1_TDU_EN
       | tdu2exu_ibrkpt_exc_req_i
`endif // SCR1_TDU_EN
    ) begin
        exu2csr_r_req_o = 1'b0;
        exu2csr_w_req_o = 1'b0;
    end else begin
        case (exu_queue.csr_cmd)
            SCR1_CSR_CMD_WRITE  : begin
                exu2csr_r_req_o = |exu_queue.rd_addr;
                exu2csr_w_req_o = csr_access_init;
            end
            SCR1_CSR_CMD_SET,
            SCR1_CSR_CMD_CLEAR  : begin
                exu2csr_r_req_o = 1'b1;
                exu2csr_w_req_o = |exu_queue.rs1_addr & csr_access_init;
            end
            default : begin
                exu2csr_r_req_o = 1'b0;
                exu2csr_w_req_o = 1'b0;
            end
        endcase
    end
end

assign exu2csr_w_cmd_o   = exu_queue.csr_cmd;
assign exu2csr_rw_addr_o = exu_queue.imm[SCR1_CSR_ADDR_WIDTH-1:0];
assign exu2csr_w_data_o  = (exu_queue.csr_op == SCR1_CSR_OP_REG)
                         ? mprf2exu_rs1_data_i
                         : {'0, exu_queue.rs1_addr}; // zimm


// CSR access FSM
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        csr_access_ff <= SCR1_CSR_INIT;
    end else begin
        csr_access_ff <= csr_access_next;
    end
end

assign csr_access_next = (csr_access_init & (csr2exu_mstatus_mie_up_i | csr2exu_sstatus_sie_up_i))
                       ? SCR1_CSR_RDY
                       : SCR1_CSR_INIT;

assign csr_access_init = (csr_access_ff == SCR1_CSR_INIT);

// CSR events interface
//------------------------------------------------------------------------------

// Exceptions signals
assign exu2csr_take_exc_o = exu_exc_req
`ifdef SCR1_DBG_EN
                          & ~hdu2exu_dbg_halted_i
`endif // SCR1_DBG_EN
                          ;
assign exu2csr_exc_code_o = exc_code;
assign exu2csr_trap_val_o = exc_trap_val;

// Interrupts signals
assign exu2csr_take_irq_o = csr2exu_irq_i & ~exu2pipe_exu_busy_o
`ifdef SCR1_DBG_EN
                          & ~hdu2exu_irq_dsbl_i
                          & ~hdu2exu_dbg_halted_i
`endif // SCR1_DBG_EN
`ifdef SCR1_CLKCTRL_EN
                          & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                          ;

// MRET signals
// MRET instruction flag
assign exu2csr_mret_instr_o  = exu_queue_vd & exu_queue.mret_req
`ifdef SCR1_TDU_EN
                             & ~tdu2exu_ibrkpt_exc_req_i
`endif // SCR1_TDU_EN
`ifdef SCR1_DBG_EN
                             & ~hdu2exu_dbg_halted_i
`endif // SCR1_DBG_EN
                             ;
assign exu2csr_mret_update_o = exu2csr_mret_instr_o & csr_access_init;

// SRET signals
// SRET instruction flag
assign exu2csr_sret_instr_o  = exu_queue_vd & exu_queue.sret_req & ~csr2exu_tsr_i
`ifdef SCR1_TDU_EN
                             & ~tdu2exu_ibrkpt_exc_req_i
`endif // SCR1_TDU_EN
`ifdef SCR1_DBG_EN
                             & ~hdu2exu_dbg_halted_i
`endif // SCR1_DBG_EN
                             ;
assign exu2csr_sret_update_o = exu2csr_sret_instr_o & csr_access_init;

`ifdef SCR1_TDU_EN
//------------------------------------------------------------------------------
// EXU <-> TDU interface
//------------------------------------------------------------------------------

// Instruction monitor
assign exu2tdu_imon_o.vd    = exu_queue_vd;
assign exu2tdu_imon_o.req   = exu2pipe_instret_o;
assign exu2tdu_imon_o.addr  = pc_curr_ff;

always_comb begin
    exu2tdu_ibrkpt_ret_o = '0;
    if (exu_queue_vd) begin
        exu2tdu_ibrkpt_ret_o = tdu2exu_ibrkpt_match_i;
        if (lsu_req) begin
            exu2tdu_ibrkpt_ret_o[SCR1_TDU_MTRIG_NUM-1:0] |= tdu2lsu_dbrkpt_match_i;
        end
    end
end
`endif // SCR1_TDU_EN


`ifdef SCR1_TRGT_SIMULATION
//------------------------------------------------------------------------------
// Tracelog signals
//------------------------------------------------------------------------------

logic [`SCR1_XLEN-1:0]      update_pc;
logic                       update_pc_en;

assign update_pc_en = (init_pc | exu2pipe_instret_o | exu2csr_take_irq_o)
`ifdef SCR1_DBG_EN
                    & ~hdu2exu_pc_advmt_dsbl_i & ~hdu2exu_no_commit_i
`endif // SCR1_DBG_EN
                    ;
assign update_pc    = exu2ifu_pc_new_req_o ? exu2ifu_pc_new_o : inc_pc;


//------------------------------------------------------------------------------
// Assertion
//------------------------------------------------------------------------------

// X checks

SCR1_SVA_EXU_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({idu2exu_req_i, csr2exu_irq_i, csr2exu_ip_ie_i, lsu_req, lsu_rdy, exu_exc_req})
    ) else $error("EXU Error: unknown control values");

SCR1_SVA_EXU_XCHECK_QUEUE : assert property (
    @(negedge clk) disable iff (~rst_n)
    (idu2exu_req_i & exu_queue_vd) |-> !$isunknown(idu2exu_cmd_i)
    ) else $error("EXU Error: unknown values in queue");

SCR1_SVA_EXU_XCHECK_CSR_RDATA : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_r_req_o |-> !$isunknown({csr2exu_r_data_i, csr2exu_rw_exc_i})
    ) else $error("EXU Error: unknown values from CSR");

// Behavior checks

SCR1_SVA_EXU_ONEHOT : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({exu_queue.jump_req, exu_queue.branch_req, lsu_req})
    ) else $error("EXU Error: illegal combination of control signals");

SCR1_SVA_EXU_ONEHOT_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu_queue_vd |->
    $onehot0({exu_queue.exc_req, lsu_exc_req, csr2exu_rw_exc_i
`ifndef SCR1_RVC_EXT
    , jb_misalign
`endif
    })
    ) else $error("EXU Error: exceptions $onehot0 failed");

// No event can request current PC update before initial reset sequence is done
SCR1_SVA_EXU_CURR_PC_UPD_BEFORE_INIT : assert property (
    @(negedge clk) disable iff (~rst_n)
    ~&init_pc_v |-> ~( pc_curr_upd & ~init_pc )
    ) else $error("EXU Error: current PC updated before been initialized");

// No event can generate a new PC request to IFU before initial reset sequence
// is done
SCR1_SVA_EXU_NEW_PC_REQ_BEFORE_INIT : assert property (
    @(negedge clk) disable iff (~rst_n)
    ~&init_pc_v |-> ~( exu2ifu_pc_new_req_o & ~init_pc )
    ) else $error("EXU Error: new PC req generated before reset sequence is done");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_exu
