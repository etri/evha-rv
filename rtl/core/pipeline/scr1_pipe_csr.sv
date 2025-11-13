/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_pipe_csr.sv>
/// @brief      Control Status Registers (CSR)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Provides access to RISC-V CSR Machine registers
 // - Handles events (EXC, IRQ and MRET):
 //   - Setups handling configuration
 //   - Displays events statuses and information
 //   - Generates new PC
 // - Provides information about the number of executed instructions and elapsed
 //   cycles
 // - Provides interfaces for IPIC, HDU and TDU registers access
 //
 // Structure:
 // - Events (EXC, IRQ, MRET) logic
 // - CSR read/write interface
 // - CSR registers:
 //   - Machine Trap Setup registers
 //   - Machine Trap Handling registers
 //   - Machine Counters/Timers registers
 //   - Non-standard CSRs (MCOUNTEN)
 // - CSR <-> EXU i/f
 // - CSR <-> IPIC i/f
 // - CSR <-> HDU i/f
 // - CSR <-> TDU i/f
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"
`include "scr1_csr.svh"
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBG_EN
`include "scr1_hdu.svh"
`endif // SCR1_DBG_EN
`ifdef SCR1_TDU_EN
`include "scr1_tdu.svh"
`endif // SCR1_TDU_EN

module scr1_pipe_csr (
    // Common
    input   logic                                       rst_n,                      // CSR reset
    input   logic                                       clk,                        // Gated CSR clock
`ifndef SCR1_CSR_REDUCED_CNT
 `ifdef SCR1_CLKCTRL_EN
    input   logic                                       clk_alw_on,                 // Not-gated CSR clock
 `endif // SCR1_CLKCTRL_EN
`endif // SCR1_CSR_REDUCED_CNT

    // SOC signals
    // IRQ
    input   logic                                       soc2csr_irq_ext_i,          // External interrupt request
    input   logic                                       soc2csr_irq_soft_i,         // Software interrupt request
    input   logic                                       soc2csr_irq_mtimer_i,       // External timer interrupt request

    // Memory-mapped external timer
    input   logic [63:0]                                soc2csr_mtimer_val_i,       // External timer value

    // MHARTID fuse
    input   logic [`SCR1_XLEN-1:0]                      soc2csr_fuse_mhartid_i,     // MHARTID fuse

    // CSR <-> EXU read/write interface
    input   logic                                       exu2csr_r_req_i,            // CSR read/write address
    input   logic [SCR1_CSR_ADDR_WIDTH-1:0]             exu2csr_rw_addr_i,          // CSR read request
    output  logic [`SCR1_XLEN-1:0]                      csr2exu_r_data_o,           // CSR read data
    input   logic                                       exu2csr_w_req_i,            // CSR write request
    input   type_scr1_csr_cmd_sel_e                     exu2csr_w_cmd_i,            // CSR write command
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_w_data_i,           // CSR write data
    output  logic                                       csr2exu_rw_exc_o,           // CSR read/write access exception
	output	logic										csr2exu_tvm_o,				// TVM enable
	output	logic										csr2exu_tsr_o,				// SRET trap

    // CSR <-> EXU event interface
    input   logic                                       exu2csr_take_irq_i,         // Take IRQ trap
    input   logic                                       exu2csr_take_exc_i,         // Take exception trap
    input   logic                                       exu2csr_mret_update_i,      // MRET update CSR
    input   logic                                       exu2csr_mret_instr_i,       // MRET instruction
    input   logic                                       exu2csr_sret_update_i,      // SRET update CSR
    input   logic                                       exu2csr_sret_instr_i,       // SRET instruction
    input   type_scr1_exc_code_e                        exu2csr_exc_code_i,         // Exception code (see scr1_arch_types.svh)
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_trap_val_i,         // Trap value
    output  logic                                       csr2exu_irq_o,              // IRQ request
    output  logic                                       csr2exu_ip_ie_o,            // Some IRQ pending and locally enabled
    output  logic                                       csr2exu_mstatus_mie_up_o,   // MSTATUS or MIE update in the current cycle
    output  logic                                       csr2exu_sstatus_sie_up_o,   // SSTATUS or SIE update in the current cycle

	// CSR <-> MMU interface
	output	logic										csr2mmu_trans_instr_o,
	output	logic										csr2mmu_trans_ldst_o,
	output	logic [1:0]									csr2mmu_priv_instr_o,
	output	logic [1:0]									csr2mmu_priv_ldst_o,
	output	logic										csr2mmu_sum_o,
	output	logic										csr2mmu_mxr_o,
	output	logic [43:0]								csr2mmu_ppn_o,
	output	logic [15:0]								csr2mmu_asid_o,

	output	logic										csr2mmu_asid_to_be_flushed_o,
	output	logic										csr2mmu_vaddr_to_be_flushed_o,

`ifdef SCR1_IPIC_EN
    // CSR <-> IPIC interface
    output  logic                                       csr2ipic_r_req_o,           // IPIC read request
    output  logic                                       csr2ipic_w_req_o,           // IPIC write request
    output  logic [2:0]                                 csr2ipic_addr_o,            // IPIC address
    output  logic [`SCR1_XLEN-1:0]                      csr2ipic_wdata_o,           // IPIC write data
    input   logic [`SCR1_XLEN-1:0]                      ipic2csr_rdata_i,           // IPIC read data
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBG_EN
    // CSR <-> HDU interface
    output  logic                                       csr2hdu_req_o,              // Request to HDU
    output  type_scr1_csr_cmd_sel_e                     csr2hdu_cmd_o,              // HDU command
    output  logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]    csr2hdu_addr_o,             // HDU address
    output  logic [`SCR1_XLEN-1:0]                      csr2hdu_wdata_o,            // HDU write data
    input   logic [`SCR1_XLEN-1:0]                      hdu2csr_rdata_i,            // HDU read data
    input   type_scr1_csr_resp_e                        hdu2csr_resp_i,             // HDU response
    input   logic                                       hdu2csr_no_commit_i,        // Forbid instruction commitment
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
    // CSR <-> TDU interface
    output  logic                                       csr2tdu_req_o,              // Request to TDU
    output  type_scr1_csr_cmd_sel_e                     csr2tdu_cmd_o,              // TDU command
    output  logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]        csr2tdu_addr_o,             // TDU address
    output  logic [`SCR1_XLEN-1:0]                      csr2tdu_wdata_o,            // TDU write data
    input   logic [`SCR1_XLEN-1:0]                      tdu2csr_rdata_i,            // TDU read data
    input   type_scr1_csr_resp_e                        tdu2csr_resp_i,             // TDU response
`endif // SCR1_TDU_EN

    // CSR <-> EXU PC interface
`ifndef SCR1_CSR_REDUCED_CNT
    input   logic                                       exu2csr_instret_no_exc_i,   // Instruction retired (without exception)
`endif // SCR1_CSR_REDUCED_CNT
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_pc_curr_i,          // Current PC
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_pc_next_i,          // Next PC
    output  logic [`SCR1_XLEN-1:0]                      csr2exu_new_pc_o,           // Exception/IRQ/MRET new PC

	output	logic [1:0]									csr2exu_mstatus_fs_o,
	input	logic										exu2csr_fpu_done_i,
	input	logic [4:0]									exu2csr_fpu_fflags_i,
	output	logic [2:0]									csr2exu_fpu_frm_o
);

//------------------------------------------------------------------------------
// Local parameters
//------------------------------------------------------------------------------

`ifdef SCR1_RVC_EXT
    localparam PC_LSB = 1;
`else
    localparam PC_LSB = 2;
`endif

typedef enum logic [1:0] {
	PRIV_U	= 2'b00,
	PRIV_S	= 2'b01,
	PRIV_M	= 2'b11
} type_scr1_priv_e;

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// Floating-point registers
//------------------------------------------------------------------------------

logic												csr_fflags_upd;
logic												csr_frm_upd;
logic												csr_fcsr_upd;

logic [4:0]											csr_fflags_next;
logic [4:0]											csr_fflags_ff;
logic [2:0]											csr_frm_next;
logic [2:0]											csr_frm_ff;

// Privilege level register
//------------------------------------------------------------------------------
type_scr1_priv_e									priv_curr;	// privilege level current value
type_scr1_priv_e									priv_next;	// privilege level next value

logic												priv_m;
logic												priv_s;
logic												priv_u;

logic												addr_priv_vd;

// Machine Trap Setup registers
//------------------------------------------------------------------------------

// MSTATUS register
logic                                               csr_mstatus_upd;        // MSTATUS update enable
logic [`SCR1_XLEN-1:0]                              csr_mstatus;            // Aggregated MSTATUS
logic                                               csr_mstatus_sie_ff;     // MSTATUS: Supervisor-level global interrupt enable
logic                                               csr_mstatus_mie_ff;     // MSTATUS: Machine-level global interrupt enable
logic                                               csr_mstatus_spie_ff;    // MSTATUS: Supervisor-level global interrupt enable prior to the trap
logic                                               csr_mstatus_mpie_ff;    // MSTATUS: Machine-level global interrupt enable prior to the trap
logic [1:0]											csr_mstatus_spp_ff;		// MSTATUS: Supervisor-level privilege level prior to the trap
logic [1:0]											csr_mstatus_mpp_ff;		// MSTATUS: Machine-level privilege level prior to the trap
logic [1:0]											csr_mstatus_fs_ff;		// MSTATUS: Floating-point status
logic												csr_mstatus_mprv_ff;	// MSTATUS: Effective privilege mode for load and store
logic												csr_mstatus_sum_ff;		// MSTATUS: Permit supervisor user memory access
logic												csr_mstatus_mxr_ff;		// MSTATUS: Make executable readable
logic												csr_mstatus_tvm_ff;		// MSTATUS: Trap virtual memory
logic [1:0]											csr_mstatus_tsr_ff;		// MSTATUS: Trap SRET control

logic                                               csr_mstatus_sie_next;   // MSTATUS: Supervisor-level global interrupt enable next value
logic                                               csr_mstatus_mie_next;   // MSTATUS: Machine-level global interrupt enable next value
logic                                               csr_mstatus_spie_next;  // MSTATUS: Supervisor-level global interrupt enable prior to the trap next value
logic                                               csr_mstatus_mpie_next;  // MSTATUS: Machine-level global interrupt enable prior to the trap next value
logic [1:0]											csr_mstatus_spp_next;	// MSTATUS: Supervisor-level privilege level prior to the trap next value
logic [1:0]											csr_mstatus_mpp_next;	// MSTATUS: Machine-level privilege level prior to the trap next value
logic [1:0]											csr_mstatus_fs_next;	// MSTATUS: Floating-point status next value
logic												csr_mstatus_mprv_next;	// MSTATUS: Effective privilege mode for load and store
logic												csr_mstatus_sum_next;	// MSTATUS: Permit supervisor user memory access
logic												csr_mstatus_mxr_next;	// MSTATUS: Make executable readable
logic												csr_mstatus_tvm_next;	// MSTATUS: Trap virtual memory
logic [1:0]											csr_mstatus_tsr_next;	// MSTATUS: Trap SRET control next value

// MEDELEG register
logic												csr_medeleg_upd;
logic [`SCR1_XLEN-1:0]								csr_medeleg;
logic [`SCR1_XLEN-1:0]								csr_medeleg_ff;

// MIDELEG register
logic												csr_mideleg_upd;
logic [`SCR1_XLEN-1:0]								csr_mideleg;
logic [`SCR1_XLEN-1:0]								csr_mideleg_ff;

logic												csr_mideleg_ssi;
logic												csr_mideleg_sti;
logic												csr_mideleg_sei;

// MIE register
logic                                               csr_mie_upd;            // MIE update enable
logic [`SCR1_XLEN-1:0]                              csr_mie;                // Aggregated MIE
logic                                               csr_mie_stie_ff;        // SIE: Supervisor timer interrupt enable
logic                                               csr_mie_mtie_ff;        // MIE: Machine timer interrupt enable
logic                                               csr_mie_seie_ff;        // SIE: Supervisor external interrupt enable
logic                                               csr_mie_meie_ff;        // MIE: Machine external interrupt enable
logic                                               csr_mie_ssie_ff;        // SIE: Supervisor software interrupt enable
logic                                               csr_mie_msie_ff;        // MIE: Machine software interrupt enable

// MTVEC register
logic                                               csr_mtvec_upd;          // MTVEC update enable
logic [`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS]  csr_mtvec_base;         // MTVEC: Base (upper 26 bits)
logic                                               csr_mtvec_mode;         // MTVEC: Mode (0-direct, 1-vectored) (wired)
`ifdef SCR1_MTVEC_MODE_EN
logic                                               csr_mtvec_mode_ff;      // MTVEC: Mode (0-direct, 1-vectored) (registered)
logic                                               csr_mtvec_mode_vect;
`endif

// Machine Trap Handling registers
//------------------------------------------------------------------------------

// MSCRATCH register
logic                                               csr_mscratch_upd;       // MSCRATCH update enable
logic [`SCR1_XLEN-1:0]                              csr_mscratch_ff;        // MSCRATCH

// MEPC register
logic                                               csr_mepc_upd;           // MEPC update enable
logic [`SCR1_XLEN-1:PC_LSB]                         csr_mepc_ff;            // MEPC registered value
logic [`SCR1_XLEN-1:PC_LSB]                         csr_mepc_next;          // MEPC next value
logic [`SCR1_XLEN-1:0]                              csr_mepc;               // MEPC registered value extended to XLEN

// MCAUSE register
logic                                               csr_mcause_upd;         // MCAUSE update enable
logic                                               csr_mcause_i_ff;        // MCAUSE: Interrupt
logic                                               csr_mcause_i_next;      // MCAUSE: Interrupt next value
type_scr1_exc_code_e                                csr_mcause_ec_ff;       // MCAUSE: Exception code
type_scr1_exc_code_e                                csr_mcause_ec_next;     // MCAUSE: Exception code next value
type_scr1_exc_code_e                                csr_mcause_ec_new;      // MCAUSE: Exception code new value (IRQs)

// MTVAL register
logic                                               csr_mtval_upd;          // MTVAL update enable
logic [`SCR1_XLEN-1:0]                              csr_mtval_ff;           // MTVAL registered value
logic [`SCR1_XLEN-1:0]                              csr_mtval_next;         // MTVAL next value

// MIP register
logic												csr_mip_upd;
logic [`SCR1_XLEN-1:0]								csr_mip_ff;
logic [`SCR1_XLEN-1:0]								csr_mip_next;

logic [`SCR1_XLEN-1:0]                              csr_mip;                // Aggregated MIP
logic                                               csr_mip_stip;           // MIP: Supervisor timer interrupt pending
logic                                               csr_mip_mtip;           // MIP: Machine timer interrupt pending
logic                                               csr_mip_seip;           // MIP: Supervisor external interrupt pending
logic                                               csr_mip_meip;           // MIP: Machine external interrupt pending
logic                                               csr_mip_ssip;           // MIP: Supervisor software interrupt pending
logic                                               csr_mip_msip;           // MIP: Machine software interrupt pending


// Supervisor Trap Setup registers
//------------------------------------------------------------------------------

// SSTATUS register
logic                                               csr_sstatus_upd;        // SSTATUS update enable
logic [`SCR1_XLEN-1:0]                              csr_sstatus;            // Aggregated SSTATUS
logic                                               csr_sstatus_sie_ff;     // SSTATUS: Supervisor-level global interrupt enable
logic                                               csr_sstatus_spie_ff;    // SSTATUS: Supervisor-level global interrupt enable prior to the trap
logic [1:0]											csr_sstatus_spp_ff;		// SSTATUS: Supervisor-level privilege level prior to the trap
logic [1:0]											csr_sstatus_fs_ff;		// SSTATUS: Floating-point status
logic												csr_sstatus_sum_ff;		// SSTATUS: Permit supervisor user memory access
logic												csr_sstatus_mxr_ff;		// SSTATUS: Make executable readable


// SIE register
logic                                               csr_sie_upd;            // SIE update enable
logic [`SCR1_XLEN-1:0]                              csr_sie;                // Aggregated SIE
logic                                               csr_sie_stie_ff;        // SIE: Supervisor timer interrupt enable
logic                                               csr_sie_seie_ff;        // SIE: Supervisor external interrupt enable
logic                                               csr_sie_ssie_ff;        // SIE: Supervisor software interrupt enable

// STVEC register
logic                                               csr_stvec_upd;          // STVEC update enable
logic [`SCR1_XLEN-1:SCR1_CSR_STVEC_BASE_ZERO_BITS]  csr_stvec_base;         // STVEC: Base (upper 26 bits)
logic                                               csr_stvec_mode;         // STVEC: Mode (0-direct, 1-vectored) (wired)
`ifdef SCR1_STVEC_MODE_EN
logic                                               csr_stvec_mode_ff;      // STVEC: Mode (0-direct, 1-vectored) (registered)
logic                                               csr_stvec_mode_vect;
`endif


// Supervisor Trap Handling registers
//------------------------------------------------------------------------------

// SSCRATCH register
logic                                               csr_sscratch_upd;       // SSCRATCH update enable
logic [`SCR1_XLEN-1:0]                              csr_sscratch_ff;        // SSCRATCH

// SEPC register
logic                                               csr_sepc_upd;           // SEPC update enable
logic [`SCR1_XLEN-1:PC_LSB]                         csr_sepc_ff;            // SEPC registered value
logic [`SCR1_XLEN-1:PC_LSB]                         csr_sepc_next;          // SEPC next value
logic [`SCR1_XLEN-1:0]                              csr_sepc;               // SEPC registered value extended to XLEN

// SIP register
logic                                               csr_sip_upd;            // SIP update enable
logic [`SCR1_XLEN-1:0]                              csr_sip;                // Aggregated SIP
logic                                               csr_sip_stip;           // SIP: Supervisor timer interrupt pending
logic                                               csr_sip_seip;           // SIP: Supervisor external interrupt pending
logic                                               csr_sip_ssip;           // SIP: Supervisor software interrupt pending

// SCAUSE register
logic                                               csr_scause_upd;         // SCAUSE update enable
logic                                               csr_scause_i_ff;        // SCAUSE: Interrupt
logic                                               csr_scause_i_next;      // SCAUSE: Interrupt next value
type_scr1_exc_code_e                                csr_scause_ec_ff;       // SCAUSE: Exception code
type_scr1_exc_code_e                                csr_scause_ec_next;     // SCAUSE: Exception code next value
type_scr1_exc_code_e                                csr_scause_ec_new;      // SCAUSE: Exception code new value (IRQs)

// STVAL register
logic                                               csr_stval_upd;          // STVAL update enable
logic [`SCR1_XLEN-1:0]                              csr_stval_ff;           // STVAL registered value
logic [`SCR1_XLEN-1:0]                              csr_stval_next;         // STVAL next value



// Supervisor Address Protection and Translation register
//------------------------------------------------------------------------------

// SATP register
logic												csr_satp_upd;
logic [`SCR1_XLEN-1:0]								csr_satp_ff;
logic [`SCR1_XLEN-1:0]								csr_satp_next;

logic [43:0]										csr_satp_ppn;
logic [15:0]										csr_satp_asid;
logic [3:0]											csr_satp_mode;

logic												satp_translation_on;
logic												instr_translation_on;
logic												ldst_translation_mprv_0;
logic												ldst_translation_mprv_1;
logic												ldst_translation_on;


// Machine Counters/Timers registers
//------------------------------------------------------------------------------

`ifndef SCR1_CSR_REDUCED_CNT
// MINSTRET register
logic [1:0]                                         csr_minstret_upd;
logic [SCR1_CSR_COUNTERS_WIDTH-1:0]                 csr_minstret;
logic                                               csr_minstret_lo_inc;
logic                                               csr_minstret_lo_upd;
logic [7:0]                                         csr_minstret_lo_ff;
logic [7:0]                                         csr_minstret_lo_next;
logic                                               csr_minstret_hi_inc;
logic                                               csr_minstret_hi_upd;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_minstret_hi_ff;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_minstret_hi_next;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_minstret_hi_new;

// MCYCLE register
logic [1:0]                                         csr_mcycle_upd;
logic [SCR1_CSR_COUNTERS_WIDTH-1:0]                 csr_mcycle;
logic                                               csr_mcycle_lo_inc;
logic                                               csr_mcycle_lo_upd;
logic [7:0]                                         csr_mcycle_lo_ff;
logic [7:0]                                         csr_mcycle_lo_next;
logic                                               csr_mcycle_hi_inc;
logic                                               csr_mcycle_hi_upd;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_mcycle_hi_ff;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_mcycle_hi_next;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_mcycle_hi_new;
`endif // ~SCR1_CSR_REDUCED_CNT

// Non-standard CSRs
//------------------------------------------------------------------------------

// MCOUNTEN register
`ifdef SCR1_MCOUNTEN_EN
logic                                               csr_mcounten_upd;       // MCOUNTEN update enable
logic [`SCR1_XLEN-1:0]                              csr_mcounten;           // Aggregated MCOUNTEN
logic                                               csr_mcounten_cy_ff;     // Cycle count enable
logic                                               csr_mcounten_ir_ff;     // Instret count enable
`endif // SCR1_MCOUNTEN_EN

// CSR read/write i/f
//------------------------------------------------------------------------------

logic [`SCR1_XLEN-1:0]                              csr_r_data;
logic [`SCR1_XLEN-1:0]                              csr_w_data;

// Events (exceptions, interrupts, mret) signals
//------------------------------------------------------------------------------

// Event flags
logic                                               e_exc;              // Successful exception trap
logic                                               e_exc_s;            // Successful exception trap delegated to S-mode
logic                                               e_irq;              // Successful IRQ trap
logic                                               e_irq_s;            // Successful IRQ trap delegated to S-mode
logic                                               e_mret;             // MRET instruction
logic                                               e_sret;             // SRET instruction
logic                                               e_irq_nmret;        // IRQ trap without MRET instruction
logic                                               e_irq_nsret;        // IRQ trap without SRET instruction

// Exception signals
type_scr1_exc_code_e                        		exc_code;
logic												exc_delegated;

// Interrupt pending & enable signals
logic												irq_m_en;
logic												irq_s_en;
logic												irq_delegated;

logic                                               csr_eirq_m_pnd_en;		// Machine external IRQ pending and locally enabled
logic                                               csr_sirq_m_pnd_en;		// Machine software IRQ pending and locally enabled
logic                                               csr_tirq_m_pnd_en;		// Machine timer IRQ pending and locally enabled
logic                                               csr_eirq_s_pnd_en;		// Supervisor external IRQ pending and locally enabled
logic                                               csr_sirq_s_pnd_en;		// Supervisor software IRQ pending and locally enabled
logic                                               csr_tirq_s_pnd_en;		// Supervisor timer IRQ pending and locally enabled
logic                                               csr_eirq_s_de_pnd_en;	// Supervisor external IRQ pending and locally enabled
logic                                               csr_sirq_s_de_pnd_en;	// Supervisor software IRQ pending and locally enabled
logic                                               csr_tirq_s_de_pnd_en;	// Supervisor timer IRQ pending and locally enabled

// CSR exception flags
logic                                               csr_w_exc;
logic                                               csr_r_exc;
logic                                               exu_req_no_exc;

// Requests to other modules
logic                                               csr_ipic_req;
`ifdef SCR1_DBG_EN
logic                                               csr_hdu_req;
`endif // SCR1_DBG_EN
`ifdef SCR1_TDU_EN
logic                                               csr_brkm_req;
`endif // SCR1_TDU_EN

//------------------------------------------------------------------------------
// Events (IRQ, EXC, MRET)
//------------------------------------------------------------------------------

// Events priority
assign e_exc    = exu2csr_take_exc_i & ~exc_delegated
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;
assign e_irq    = exu2csr_take_irq_i & ~exu2csr_take_exc_i & ~irq_delegated
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;

assign e_exc_s  = exu2csr_take_exc_i & exc_delegated
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;
assign e_irq_s  = exu2csr_take_irq_i & ~exu2csr_take_exc_i & irq_delegated
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;

assign e_mret   = exu2csr_mret_update_i
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;
assign e_sret   = exu2csr_sret_update_i
`ifdef SCR1_DBG_EN
                & ~hdu2csr_no_commit_i
`endif // SCR1_DBG_EN
                ;
assign e_irq_nmret = (e_irq | e_irq_s) & ~exu2csr_mret_instr_i;
assign e_irq_nsret = (e_irq | e_irq_s) & ~exu2csr_sret_instr_i;

// Delegated exception check
always_comb begin
	case (exu2csr_exc_code_i)
		SCR1_EXC_CODE_INSTR_MISALIGN        : exc_code = exu2csr_exc_code_i;
    	SCR1_EXC_CODE_INSTR_ACCESS_FAULT    : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_ILLEGAL_INSTR         : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_BREAKPOINT            : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_LD_ADDR_MISALIGN      : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_LD_ACCESS_FAULT       : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_ST_ADDR_MISALIGN      : exc_code = exu2csr_exc_code_i; 
    	SCR1_EXC_CODE_ST_ACCESS_FAULT       : exc_code = exu2csr_exc_code_i; 
		SCR1_EXC_CODE_ECALL_M & priv_u      : exc_code = SCR1_EXC_CODE_ECALL_U;
		SCR1_EXC_CODE_ECALL_M & priv_s      : exc_code = SCR1_EXC_CODE_ECALL_S;
		SCR1_EXC_CODE_ECALL_M & priv_m      : exc_code = SCR1_EXC_CODE_ECALL_M;
		default								: exc_code = exu2csr_exc_code_i;
	endcase
end

always_comb begin
	case (exc_code)
		SCR1_EXC_CODE_INSTR_MISALIGN        : exc_delegated	= csr_medeleg[0];
    	SCR1_EXC_CODE_INSTR_ACCESS_FAULT    : exc_delegated	= csr_medeleg[1]; 
    	SCR1_EXC_CODE_ILLEGAL_INSTR         : exc_delegated	= csr_medeleg[2]; 
    	SCR1_EXC_CODE_BREAKPOINT            : exc_delegated	= csr_medeleg[3]; 
    	SCR1_EXC_CODE_LD_ADDR_MISALIGN      : exc_delegated	= csr_medeleg[4]; 
    	SCR1_EXC_CODE_LD_ACCESS_FAULT       : exc_delegated	= csr_medeleg[5]; 
    	SCR1_EXC_CODE_ST_ADDR_MISALIGN      : exc_delegated	= csr_medeleg[6]; 
    	SCR1_EXC_CODE_ST_ACCESS_FAULT       : exc_delegated	= csr_medeleg[7]; 
		SCR1_EXC_CODE_ECALL_U               : exc_delegated = csr_medeleg[8];
		SCR1_EXC_CODE_ECALL_S               : exc_delegated = csr_medeleg[9];
		SCR1_EXC_CODE_ECALL_M               : exc_delegated = csr_medeleg[11];
		default								: exc_delegated = 1'b0;
	endcase
end

// IRQ pending & enable signals

assign irq_m_en				= (priv_m & csr_mstatus_mie_ff)
							| priv_s
							| priv_u;
assign irq_s_en				= (priv_s & csr_sstatus_sie_ff)
							| priv_u;

assign irq_delegated		= csr_eirq_s_de_pnd_en
							| csr_sirq_s_de_pnd_en
							| csr_tirq_s_de_pnd_en
							;

assign csr_eirq_m_pnd_en 	= (irq_m_en & csr_mip_meip & csr_mie_meie_ff);
assign csr_sirq_m_pnd_en 	= (irq_m_en & csr_mip_msip & csr_mie_msie_ff);
assign csr_tirq_m_pnd_en 	= (irq_m_en & csr_mip_mtip & csr_mie_mtie_ff);

assign csr_eirq_s_pnd_en 	= (irq_m_en & csr_mip_seip & csr_mie_seie_ff & ~csr_mideleg_sei);
assign csr_sirq_s_pnd_en 	= (irq_m_en & csr_mip_ssip & csr_mie_ssie_ff & ~csr_mideleg_ssi);
assign csr_tirq_s_pnd_en 	= (irq_m_en & csr_mip_stip & csr_mie_stie_ff & ~csr_mideleg_sti);

assign csr_eirq_s_de_pnd_en	= (irq_s_en & csr_sip_seip & csr_sie_seie_ff);
assign csr_sirq_s_de_pnd_en	= (irq_s_en & csr_sip_ssip & csr_sie_ssie_ff);
assign csr_tirq_s_de_pnd_en	= (irq_s_en & csr_sip_stip & csr_sie_stie_ff);

assign csr2exu_ip_ie_o  	= (csr_mip_meip & csr_mie_meie_ff)
							| (csr_mip_msip & csr_mie_msie_ff)
							| (csr_mip_mtip & csr_mie_mtie_ff)
							| (csr_mip_seip & csr_mie_seie_ff)
							| (csr_mip_ssip & csr_mie_ssie_ff)
							| (csr_mip_stip & csr_mie_stie_ff)
							;


// IRQ exception codes priority
always_comb begin
    case (1'b1)
        csr_eirq_m_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_EXTERNAL);
        csr_sirq_m_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_SOFTWARE);
        csr_tirq_m_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_TIMER);
        csr_eirq_s_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_EXTERNAL);
        csr_sirq_s_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_SOFTWARE);
        csr_tirq_s_pnd_en	: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_TIMER);
        default        		: csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_EXTERNAL);
    endcase
end

always_comb begin
    case (1'b1)
        csr_eirq_s_de_pnd_en	: csr_scause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_EXTERNAL);
        csr_sirq_s_de_pnd_en	: csr_scause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_SOFTWARE);
        csr_tirq_s_de_pnd_en	: csr_scause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_S_TIMER);
        default        			: csr_scause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_EXTERNAL);
    endcase
end

assign exu_req_no_exc = ((exu2csr_r_req_i & ~csr_r_exc)
                      |  (exu2csr_w_req_i & ~csr_w_exc));

//------------------------------------------------------------------------------
// CSR read/write interface
//------------------------------------------------------------------------------

// privilege check

assign	addr_priv_vd	= ((exu2csr_rw_addr_i[9:8] == 2'b00) & (priv_m | priv_s | priv_u))
						| ((exu2csr_rw_addr_i[9:8] == 2'b01) & (priv_m | priv_s))
						| ((exu2csr_rw_addr_i[9:8] == 2'b11) & (priv_m))
						;

// CSR read logic
//------------------------------------------------------------------------------

always_comb begin
    csr_r_data     = '0;
    csr_r_exc      = 1'b0;
`ifdef SCR1_DBG_EN
    csr_hdu_req    = 1'b0;
`endif // SCR1_DBG_EN
`ifdef SCR1_TDU_EN
    csr_brkm_req   = 1'b0;
`endif // SCR1_TDU_EN
`ifdef SCR1_IPIC_EN
    csr2ipic_r_req_o = 1'b0;
`endif // SCR1_IPIC_EN

	case (addr_priv_vd)
		1'b0	: csr_r_exc   = exu2csr_r_req_i;
		1'b1	: begin
			casez (exu2csr_rw_addr_i)
				// Floating-point (read-write)
				SCR1_CSR_ADDR_FFLAGS	: csr_r_data	= csr_fflags_ff;
				SCR1_CSR_ADDR_FRM		: csr_r_data	= csr_frm_ff;
				SCR1_CSR_ADDR_FCSR		: csr_r_data	= {32'd0, 24'd0, csr_frm_ff, csr_fflags_ff};

				// Machine Information Registers (read-only)
				SCR1_CSR_ADDR_MVENDORID : csr_r_data    = SCR1_CSR_MVENDORID;
				SCR1_CSR_ADDR_MARCHID   : csr_r_data    = SCR1_CSR_MARCHID;
				SCR1_CSR_ADDR_MIMPID    : csr_r_data    = SCR1_CSR_MIMPID;
				SCR1_CSR_ADDR_MHARTID   : csr_r_data    = soc2csr_fuse_mhartid_i;

				// Machine Trap Setup (read-write)
				SCR1_CSR_ADDR_MSTATUS   : csr_r_data    = csr_mstatus;
				SCR1_CSR_ADDR_MISA      : csr_r_data    = SCR1_CSR_MISA;
				SCR1_CSR_ADDR_MEDELEG	: csr_r_data	= csr_medeleg;
				SCR1_CSR_ADDR_MIDELEG	: csr_r_data	= csr_mideleg;
				SCR1_CSR_ADDR_MIE       : csr_r_data    = csr_mie;
				SCR1_CSR_ADDR_MTVEC     : csr_r_data    = {csr_mtvec_base[`SCR1_XLEN-1:2], 2'(csr_mtvec_mode)};

				// Machine Trap Handling (read-write)
				SCR1_CSR_ADDR_MSCRATCH  : csr_r_data    = csr_mscratch_ff;
				SCR1_CSR_ADDR_MEPC      : csr_r_data    = csr_mepc;
				SCR1_CSR_ADDR_MCAUSE    : csr_r_data    = {csr_mcause_i_ff, type_scr1_csr_mcause_ec_v'(csr_mcause_ec_ff)};
				SCR1_CSR_ADDR_MTVAL     : csr_r_data    = csr_mtval_ff;
				SCR1_CSR_ADDR_MIP       : csr_r_data    = csr_mip_ff;

				// Supervisor Trap Setup (read-write)
				SCR1_CSR_ADDR_SSTATUS	: csr_r_data	= csr_sstatus;
				SCR1_CSR_ADDR_SIE		: csr_r_data	= csr_sie;
				SCR1_CSR_ADDR_STVEC		: csr_r_data	= {csr_stvec_base[`SCR1_XLEN-1:2], 2'(csr_stvec_mode)};

				// Supervisor Trap handling (read-write)
				SCR1_CSR_ADDR_SSCRATCH	: csr_r_data	= csr_sscratch_ff;
				SCR1_CSR_ADDR_SEPC		: csr_r_data	= csr_sepc;
				SCR1_CSR_ADDR_SCAUSE	: csr_r_data	= {csr_scause_i_ff, type_scr1_csr_mcause_ec_v'(csr_scause_ec_ff)};
				SCR1_CSR_ADDR_STVAL		: csr_r_data	= csr_stval_ff;
				SCR1_CSR_ADDR_SIP		: csr_r_data	= csr_sip;

				// Supervisor Address Protection and Translation (read-write)
				SCR1_CSR_ADDR_SATP		: begin
					case (csr_mstatus_tvm_ff)
						1'b0	: csr_r_data	= csr_satp_ff;
						1'b1	: csr_r_exc   = exu2csr_r_req_i;
					endcase
				end

				// User Counters/Timers (read-only)
				{SCR1_CSR_ADDR_HPMCOUNTER_MASK, 5'b?????}   : begin
					case (exu2csr_rw_addr_i[4:0])
						5'd1        : csr_r_data    = soc2csr_mtimer_val_i[31:0];
		`ifndef SCR1_CSR_REDUCED_CNT
						5'd0        : csr_r_data    = csr_mcycle[31:0];
						5'd2        : csr_r_data    = csr_minstret[31:0];
		`endif // SCR1_CSR_REDUCED_CNT
						default     : begin
							// return 0
						end
					endcase
				end

				{SCR1_CSR_ADDR_HPMCOUNTERH_MASK, 5'b?????}  : begin
					case (exu2csr_rw_addr_i[4:0])
						5'd1        : csr_r_data    = soc2csr_mtimer_val_i[63:32];
		`ifndef SCR1_CSR_REDUCED_CNT
						5'd0        : csr_r_data    = csr_mcycle[63:32];
						5'd2        : csr_r_data    = csr_minstret[63:32];
		`endif // SCR1_CSR_REDUCED_CNT
						default     : begin
							// return 0
						end
					endcase
				end

				// Machine Counters/Timers (read-write)
				{SCR1_CSR_ADDR_MHPMCOUNTER_MASK, 5'b?????}  : begin
					case (exu2csr_rw_addr_i[4:0])
						5'd1        : csr_r_exc     = exu2csr_r_req_i;
		`ifndef SCR1_CSR_REDUCED_CNT
						5'd0        : csr_r_data    = csr_mcycle[31:0];
						5'd2        : csr_r_data    = csr_minstret[31:0];
		`endif // SCR1_CSR_REDUCED_CNT
						default     : begin
							// return 0
						end
					endcase
				end

				{SCR1_CSR_ADDR_MHPMCOUNTERH_MASK, 5'b?????} : begin
					case (exu2csr_rw_addr_i[4:0])
						5'd1        : csr_r_exc     = exu2csr_r_req_i;
		`ifndef SCR1_CSR_REDUCED_CNT
						5'd0        : csr_r_data    = csr_mcycle[63:32];
						5'd2        : csr_r_data    = csr_minstret[63:32];
		`endif // SCR1_CSR_REDUCED_CNT
						default     : begin
							// return 0
						end
					endcase
				end

				{SCR1_CSR_ADDR_MHPMEVENT_MASK, 5'b?????}    : begin
					case (exu2csr_rw_addr_i[4:0])
						5'd0,
						5'd1,
						5'd2        : csr_r_exc = exu2csr_r_req_i;
						default     : begin
							// return 0
						end
					endcase
				end

		`ifdef SCR1_MCOUNTEN_EN
				SCR1_CSR_ADDR_MCOUNTEN      : csr_r_data    = csr_mcounten;
		`endif // SCR1_MCOUNTEN_EN

		`ifdef SCR1_IPIC_EN
				// IPIC registers
				SCR1_CSR_ADDR_IPIC_CISV,
				SCR1_CSR_ADDR_IPIC_CICSR,
				SCR1_CSR_ADDR_IPIC_IPR,
				SCR1_CSR_ADDR_IPIC_ISVR,
				SCR1_CSR_ADDR_IPIC_EOI,
				SCR1_CSR_ADDR_IPIC_SOI,
				SCR1_CSR_ADDR_IPIC_IDX,
				SCR1_CSR_ADDR_IPIC_ICSR     : begin
					csr_r_data       = ipic2csr_rdata_i;
					csr2ipic_r_req_o = exu2csr_r_req_i;
				end
		`endif // SCR1_IPIC_EN

		`ifdef SCR1_DBG_EN
				// HDU registers
				SCR1_HDU_DBGCSR_ADDR_DCSR,
				SCR1_HDU_DBGCSR_ADDR_DPC,
				SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
				SCR1_HDU_DBGCSR_ADDR_DSCRATCH1 : begin
					csr_hdu_req = 1'b1;
					csr_r_data  = hdu2csr_rdata_i;
				end
		`endif // SCR1_DBG_EN

		`ifdef SCR1_TDU_EN
				// TDU registers
				SCR1_CSR_ADDR_TDU_TSELECT,
				SCR1_CSR_ADDR_TDU_TDATA1,
				SCR1_CSR_ADDR_TDU_TDATA2,
				SCR1_CSR_ADDR_TDU_TINFO,
				SCR1_CSR_ADDR_TDU_TCONTROL: begin
					csr_brkm_req    = 1'b1;
					csr_r_data      = tdu2csr_rdata_i;
				end
		`endif // SCR1_TDU_EN

				default     : begin
					csr_r_exc   = exu2csr_r_req_i;
				end
			endcase // exu2csr_rw_addr_i
		end
	endcase
end

assign csr2exu_r_data_o = csr_r_data;

// CSR write logic
//------------------------------------------------------------------------------

always_comb begin
    case (exu2csr_w_cmd_i)
        SCR1_CSR_CMD_WRITE  : csr_w_data =  exu2csr_w_data_i;
        SCR1_CSR_CMD_SET    : csr_w_data =  exu2csr_w_data_i | csr_r_data;
        SCR1_CSR_CMD_CLEAR  : csr_w_data = ~exu2csr_w_data_i & csr_r_data;
        default             : csr_w_data = '0;
    endcase
end

always_comb begin
	csr_fflags_upd		= 1'b0;
	csr_frm_upd			= 1'b0;
	csr_fcsr_upd		= 1'b0;

    csr_mstatus_upd     = 1'b0;
	csr_medeleg_upd		= 1'b0;
	csr_mideleg_upd		= 1'b0;
    csr_mie_upd         = 1'b0;
    csr_mtvec_upd       = 1'b0;
    csr_mscratch_upd    = 1'b0;
    csr_mepc_upd        = 1'b0;
    csr_mcause_upd      = 1'b0;
    csr_mtval_upd       = 1'b0;
	csr_mip_upd			= 1'b0;

	csr_sstatus_upd		= 1'b0;
	csr_sie_upd			= 1'b0;
	csr_stvec_upd		= 1'b0;
	csr_sscratch_upd	= 1'b0;
	csr_sepc_upd		= 1'b0;
	csr_scause_upd		= 1'b0;
	csr_stval_upd		= 1'b0;
	csr_sip_upd			= 1'b0;

	csr_satp_upd		= 1'b0;

`ifndef SCR1_CSR_REDUCED_CNT
    csr_mcycle_upd      = 2'b00;
    csr_minstret_upd    = 2'b00;
`endif // SCR1_CSR_REDUCED_CNT

`ifdef SCR1_MCOUNTEN_EN
    csr_mcounten_upd    = 1'b0;
`endif // SCR1_MCOUNTEN_EN
    csr_w_exc           = 1'b0;
`ifdef SCR1_IPIC_EN
    csr2ipic_w_req_o    = 1'b0;
`endif // SCR1_IPIC_EN

    if (exu2csr_w_req_i) begin
		case (addr_priv_vd)
			1'b0	: csr_w_exc   = 1'b1;
			1'b1	: begin
				casez (exu2csr_rw_addr_i)
					// Floating-point (read-write)
					SCR1_CSR_ADDR_FFLAGS	: csr_fflags_upd	= 1'b1;
					SCR1_CSR_ADDR_FRM		: csr_frm_upd		= 1'b1;
					SCR1_CSR_ADDR_FCSR		: csr_fcsr_upd		= 1'b1;

					// Machine Trap Setup (read-write)
					SCR1_CSR_ADDR_MSTATUS   : csr_mstatus_upd   = 1'b1;
					SCR1_CSR_ADDR_MISA      : begin end
					SCR1_CSR_ADDR_MEDELEG	: csr_medeleg_upd	= 1'b1;
					SCR1_CSR_ADDR_MIDELEG	: csr_mideleg_upd	= 1'b1;
					SCR1_CSR_ADDR_MIE       : csr_mie_upd       = 1'b1;
					SCR1_CSR_ADDR_MTVEC     : csr_mtvec_upd     = 1'b1;

					// Machine Trap Handling (read-write)
					SCR1_CSR_ADDR_MSCRATCH  : csr_mscratch_upd  = 1'b1;
					SCR1_CSR_ADDR_MEPC      : csr_mepc_upd      = 1'b1;
					SCR1_CSR_ADDR_MCAUSE    : csr_mcause_upd    = 1'b1;
					SCR1_CSR_ADDR_MTVAL     : csr_mtval_upd     = 1'b1;
					SCR1_CSR_ADDR_MIP       : csr_mip_upd		= 1'b1;

					// Supervisor Trap Setup (read-write)
					SCR1_CSR_ADDR_SSTATUS	: csr_sstatus_upd	= 1'b1;
					SCR1_CSR_ADDR_SIE		: csr_sie_upd		= 1'b1;
					SCR1_CSR_ADDR_STVEC		: csr_stvec_upd		= 1'b1;

					// Supervisor Trap Handling (read-write)
					SCR1_CSR_ADDR_SSCRATCH	: csr_sscratch_upd	= 1'b1;
					SCR1_CSR_ADDR_SEPC		: csr_sepc_upd		= 1'b1;
					SCR1_CSR_ADDR_SCAUSE	: csr_scause_upd	= 1'b1;
					SCR1_CSR_ADDR_STVAL		: csr_stval_upd		= 1'b1;
					SCR1_CSR_ADDR_SIP		: csr_sip_upd		= 1'b1;

					// Supervisor Protection and Translation (read-write)
					SCR1_CSR_ADDR_SATP		: begin
						case (csr_mstatus_tvm_ff)
							1'b0	: csr_satp_upd		= 1'b1;
							1'b1	: csr_w_exc   		= exu2csr_r_req_i;
						endcase
					end

					// Machine Counters/Timers (read-write)
					{SCR1_CSR_ADDR_MHPMCOUNTER_MASK, 5'b?????}  : begin
						case (exu2csr_rw_addr_i[4:0])
							5'd1        : csr_w_exc           = 1'b1;
		`ifndef SCR1_CSR_REDUCED_CNT
							5'd0        : csr_mcycle_upd[0]   = 1'b1;
							5'd2        : csr_minstret_upd[0] = 1'b1;
		`endif // SCR1_CSR_REDUCED_CNT
							default     : begin
								// no exception
							end
						endcase
					end

					{SCR1_CSR_ADDR_MHPMCOUNTERH_MASK, 5'b?????} : begin
						case (exu2csr_rw_addr_i[4:0])
							5'd1        : csr_w_exc           = 1'b1;
		`ifndef SCR1_CSR_REDUCED_CNT
							5'd0        : csr_mcycle_upd[1]   = 1'b1;
							5'd2        : csr_minstret_upd[1] = 1'b1;
		`endif // SCR1_CSR_REDUCED_CNT
							default     : begin
								// no exception
							end
						endcase
					end

					{SCR1_CSR_ADDR_MHPMEVENT_MASK, 5'b?????}    : begin
						case (exu2csr_rw_addr_i[4:0])
							5'd0,
							5'd1,
							5'd2        : csr_w_exc = 1'b1;
							default     : begin
								// no exception
							end
						endcase
					end

		`ifdef SCR1_MCOUNTEN_EN
					SCR1_CSR_ADDR_MCOUNTEN      : csr_mcounten_upd = 1'b1;
		`endif // SCR1_MCOUNTEN_EN

		`ifdef SCR1_IPIC_EN
					// IPIC registers
					SCR1_CSR_ADDR_IPIC_CICSR,
					SCR1_CSR_ADDR_IPIC_IPR,
					SCR1_CSR_ADDR_IPIC_EOI,
					SCR1_CSR_ADDR_IPIC_SOI,
					SCR1_CSR_ADDR_IPIC_IDX,
					SCR1_CSR_ADDR_IPIC_ICSR     : begin
						csr2ipic_w_req_o  = 1'b1;
					end
					SCR1_CSR_ADDR_IPIC_CISV,
					SCR1_CSR_ADDR_IPIC_ISVR     : begin
						// no exception on write
					end
		`endif // SCR1_IPIC_EN

		`ifdef SCR1_DBG_EN
					SCR1_HDU_DBGCSR_ADDR_DCSR,
					SCR1_HDU_DBGCSR_ADDR_DPC,
					SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
					SCR1_HDU_DBGCSR_ADDR_DSCRATCH1 : begin
					end
		`endif // SCR1_DBG_EN

		`ifdef SCR1_TDU_EN
					// TDU registers
					SCR1_CSR_ADDR_TDU_TSELECT,
					SCR1_CSR_ADDR_TDU_TDATA1,
					SCR1_CSR_ADDR_TDU_TDATA2,
					SCR1_CSR_ADDR_TDU_TINFO,
					SCR1_CSR_ADDR_TDU_TCONTROL: begin
					end
		`endif // SCR1_TDU_EN

					default : begin
						csr_w_exc   = 1'b1;
					end
				endcase
			end
		endcase
    end
end

//------------------------------------------------------------------------------
// Floating-point registers
//------------------------------------------------------------------------------

// MSTATUS
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
		csr_mstatus_fs_ff	<= SCR1_CSR_MSTATUS_FS_RST_VAL;
    end else begin
		csr_mstatus_fs_ff	<= csr_mstatus_fs_next;
    end
end

always_comb begin
    case (1'b1)
        csr_mstatus_upd	: csr_mstatus_fs_next	  = csr_w_data[SCR1_CSR_MSTATUS_FS_OFFSET+:2];
        csr_sstatus_upd	: csr_mstatus_fs_next	  = csr_w_data[SCR1_CSR_MSTATUS_FS_OFFSET+:2];
        default			: csr_mstatus_fs_next	  = csr_mstatus_fs_ff;
    endcase
end

// FCSR
always_ff @(negedge rst_n, posedge clk) begin
	if (~rst_n) begin
		csr_fflags_ff	<= '0;
		csr_frm_ff		<= '0;
	end
	else begin
		csr_fflags_ff	<= csr_fflags_next;
		csr_frm_ff		<= csr_frm_next;
	end
end

always_comb begin
	case (1'b1)
		csr_fflags_upd		: begin
			csr_frm_next					= csr_frm_ff;
			csr_fflags_next					= csr_w_data[4:0];
		end
		csr_frm_upd			: begin
			csr_frm_next					= csr_w_data[2:0];
			csr_fflags_next					= csr_fflags_ff;
		end
		csr_fcsr_upd		: begin
			{csr_frm_next, csr_fflags_next}	= csr_w_data[7:0];
		end
		exu2csr_fpu_done_i	: begin
			csr_frm_next					= csr_frm_ff;
			csr_fflags_next					= exu2csr_fpu_fflags_i;
		end
		default				: begin
			{csr_frm_next, csr_fflags_next}	= {csr_frm_ff, csr_fflags_ff};
		end
	endcase
end

assign csr2exu_fpu_frm_o	= csr_frm_ff;

assign csr2exu_mstatus_fs_o	= csr_mstatus_fs_ff;


//------------------------------------------------------------------------------
// Privilege Level registers
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		priv_curr		<= PRIV_M;
	end	
	else begin
		priv_curr		<= priv_next;
	end
end

always_comb begin
	case (1'b1)
		e_exc, 
		e_irq		: priv_next		= PRIV_M;
		e_exc_s,
		e_irq_s		: priv_next		= PRIV_S;
		e_mret		: priv_next		= type_scr1_priv_e'(csr_mstatus_mpp_ff);
		e_sret		: priv_next		= type_scr1_priv_e'(csr_mstatus_spp_ff);
		default		: priv_next		= priv_curr;
	endcase
end

assign	priv_m	= (priv_curr == PRIV_M);
assign	priv_s	= (priv_curr == PRIV_S);
assign	priv_u	= (priv_curr == PRIV_U);


//------------------------------------------------------------------------------
// Machine Trap Setup registers
//------------------------------------------------------------------------------


// MSTATUS register
//------------------------------------------------------------------------------
// MIE, MPIE : Machine-mode current and previous (before trap) global interrupt enable bits
// SIE, SPIE : Supervisor-mode current and previous (before trap) global interrupt enable bits
// MPP, SPP : Machine-mode/Supervisor-mode previous (before trap) privilege level
// TSR : Trap SRET control
// SSTATUS is subset of MSTATUS

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mstatus_mie_ff  <= SCR1_CSR_MSTATUS_MIE_RST_VAL;
        csr_mstatus_mpie_ff <= SCR1_CSR_MSTATUS_MPIE_RST_VAL;
		csr_mstatus_mpp_ff	<= SCR1_CSR_MSTATUS_MPP_RST_VAL;
		csr_mstatus_mprv_ff	<= '0;
		csr_mstatus_sum_ff	<= '0;
		csr_mstatus_mxr_ff	<= '0;
		csr_mstatus_tvm_ff	<= '0;
		csr_mstatus_tsr_ff	<= '0;
    end else begin
        csr_mstatus_mie_ff  <= csr_mstatus_mie_next;
        csr_mstatus_mpie_ff <= csr_mstatus_mpie_next;
		csr_mstatus_mpp_ff	<= csr_mstatus_mpp_next;
		csr_mstatus_mprv_ff	<= csr_mstatus_mprv_next;
		csr_mstatus_sum_ff	<= csr_mstatus_sum_next;
		csr_mstatus_mxr_ff	<= csr_mstatus_mxr_next;
		csr_mstatus_tvm_ff	<= csr_mstatus_tvm_next;
		csr_mstatus_tsr_ff	<= csr_mstatus_tsr_next;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mstatus_sie_ff  <= SCR1_CSR_MSTATUS_SIE_RST_VAL;
        csr_mstatus_spie_ff <= SCR1_CSR_MSTATUS_SPIE_RST_VAL;
		csr_mstatus_spp_ff	<= SCR1_CSR_MSTATUS_SPP_RST_VAL;
    end else begin
        csr_mstatus_sie_ff  <= csr_mstatus_sie_next;
        csr_mstatus_spie_ff <= csr_mstatus_spie_next;
		csr_mstatus_spp_ff	<= csr_mstatus_spp_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc, e_irq		: begin
            csr_mstatus_mie_next  = 1'b0;
            csr_mstatus_mpie_next = csr_mstatus_mie_ff;
			csr_mstatus_mpp_next  = priv_curr;
        end
		e_exc_s, e_irq_s	: begin
			csr_mstatus_sie_next  = 1'b0;
			csr_mstatus_spie_next = csr_mstatus_sie_ff;
			csr_mstatus_spp_next  = priv_curr;
		end
        e_mret        		: begin
            csr_mstatus_mie_next  = csr_mstatus_mpie_ff;
            csr_mstatus_mpie_next = 1'b1;
			csr_mstatus_mpp_next  = 2'b00;
        end
		e_sret		  		: begin
            csr_mstatus_sie_next  = csr_mstatus_spie_ff;
            csr_mstatus_spie_next = 1'b1;
			csr_mstatus_spp_next  = 2'b00;
		end
        csr_mstatus_upd		: begin
            csr_mstatus_mie_next  = csr_w_data[SCR1_CSR_MSTATUS_MIE_OFFSET];
            csr_mstatus_mpie_next = csr_w_data[SCR1_CSR_MSTATUS_MPIE_OFFSET];
			csr_mstatus_mpp_next  = csr_w_data[SCR1_CSR_MSTATUS_MPP_OFFSET+:2];
            csr_mstatus_sie_next  = csr_w_data[SCR1_CSR_MSTATUS_SIE_OFFSET];
            csr_mstatus_spie_next = csr_w_data[SCR1_CSR_MSTATUS_SPIE_OFFSET];
			csr_mstatus_spp_next  = csr_w_data[SCR1_CSR_MSTATUS_SPP_OFFSET+:2];
			csr_mstatus_mprv_next = csr_w_data[SCR1_CSR_MSTATUS_MPRV_OFFSET];
			csr_mstatus_sum_next  = csr_w_data[SCR1_CSR_MSTATUS_SUM_OFFSET];
			csr_mstatus_mxr_next  = csr_w_data[SCR1_CSR_MSTATUS_MXR_OFFSET];
			csr_mstatus_tvm_next  = csr_w_data[SCR1_CSR_MSTATUS_TVM_OFFSET];
			csr_mstatus_tsr_next  = csr_w_data[SCR1_CSR_MSTATUS_TSR_OFFSET];
        end
        csr_sstatus_upd		: begin
            csr_mstatus_sie_next  = csr_w_data[SCR1_CSR_MSTATUS_SIE_OFFSET];
            csr_mstatus_spie_next = csr_w_data[SCR1_CSR_MSTATUS_SPIE_OFFSET];
			csr_mstatus_spp_next  = csr_w_data[SCR1_CSR_MSTATUS_SPP_OFFSET+:2];
			csr_mstatus_sum_next  = csr_w_data[SCR1_CSR_MSTATUS_SUM_OFFSET];
			csr_mstatus_mxr_next  = csr_w_data[SCR1_CSR_MSTATUS_MXR_OFFSET];
        end
        default       		: begin
            csr_mstatus_mie_next  = csr_mstatus_mie_ff;
            csr_mstatus_mpie_next = csr_mstatus_mpie_ff;
			csr_mstatus_mpp_next  = csr_mstatus_mpp_ff;
            csr_mstatus_sie_next  = csr_mstatus_sie_ff;
            csr_mstatus_spie_next = csr_mstatus_spie_ff;
			csr_mstatus_spp_next  = csr_mstatus_spp_ff;
			csr_mstatus_mprv_next = csr_mstatus_mprv_ff;
			csr_mstatus_sum_next  = csr_mstatus_sum_ff;
			csr_mstatus_mxr_next  = csr_mstatus_mxr_ff;
			csr_mstatus_tvm_next  = csr_mstatus_tvm_ff;
			csr_mstatus_tsr_next  = csr_mstatus_tsr_ff;
        end
    endcase
end

always_comb begin
    csr_mstatus                                                            	= '0;
    csr_mstatus[SCR1_CSR_MSTATUS_MIE_OFFSET]                               	= csr_mstatus_mie_ff;
    csr_mstatus[SCR1_CSR_MSTATUS_MPIE_OFFSET]                              	= csr_mstatus_mpie_ff;
    csr_mstatus[SCR1_CSR_MSTATUS_MPP_OFFSET+1:SCR1_CSR_MSTATUS_MPP_OFFSET] 	= csr_mstatus_mpp_ff;
    csr_mstatus[SCR1_CSR_MSTATUS_SIE_OFFSET]                               	= csr_mstatus_sie_ff;
    csr_mstatus[SCR1_CSR_MSTATUS_SPIE_OFFSET]                              	= csr_mstatus_spie_ff;
    csr_mstatus[SCR1_CSR_MSTATUS_SPP_OFFSET+1:SCR1_CSR_MSTATUS_SPP_OFFSET] 	= csr_mstatus_spp_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_FS_OFFSET+:2]								= csr_mstatus_fs_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_MPRV_OFFSET]								= csr_mstatus_mprv_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_SUM_OFFSET]								= csr_mstatus_sum_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_MXR_OFFSET]								= csr_mstatus_mxr_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_TVM_OFFSET]								= csr_mstatus_tvm_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_TSR_OFFSET]								= csr_mstatus_tsr_ff;
	csr_mstatus[SCR1_CSR_MSTATUS_UXL_OFFSET+:2]								= SCR1_MISA_MXL_64;
	csr_mstatus[SCR1_CSR_MSTATUS_SXL_OFFSET+:2]								= SCR1_MISA_MXL_64;
end

assign csr2exu_tvm_o	= csr_mstatus_tvm_ff;
assign csr2exu_tsr_o	= csr_mstatus_tsr_ff;

// MEDELEG, MIDELEG register
//------------------------------------------------------------------------------
// Machine Trap Delegation Registers

always_ff @(negedge rst_n, posedge clk) begin
	if (~rst_n) begin
		csr_medeleg_ff	<= '0;
	end
	else if (csr_medeleg_upd) begin
		csr_medeleg_ff	<= csr_w_data;
	end
end

always_ff @(negedge rst_n, posedge clk) begin
	if (~rst_n) begin
		csr_mideleg_ff	<= '0;
	end
	else if (csr_mideleg_upd) begin
		csr_mideleg_ff	<= csr_w_data;
	end
end

always_comb begin
	csr_medeleg			= csr_medeleg_ff;

	csr_mideleg			= '0;
	csr_mideleg_ssi		= csr_mideleg_ff[SCR1_CSR_MIE_SSIE_OFFSET];
	csr_mideleg_sti		= csr_mideleg_ff[SCR1_CSR_MIE_STIE_OFFSET];
	csr_mideleg_sei		= csr_mideleg_ff[SCR1_CSR_MIE_SEIE_OFFSET];
end


// MIE register
//------------------------------------------------------------------------------
// Contains interrupt enable bits (external, software, timer IRQs)

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mie_stie_ff <= SCR1_CSR_MIE_STIE_RST_VAL;
        csr_mie_mtie_ff <= SCR1_CSR_MIE_MTIE_RST_VAL;
        csr_mie_seie_ff <= SCR1_CSR_MIE_SEIE_RST_VAL;
        csr_mie_meie_ff <= SCR1_CSR_MIE_MEIE_RST_VAL;
        csr_mie_ssie_ff <= SCR1_CSR_MIE_SSIE_RST_VAL;
        csr_mie_msie_ff <= SCR1_CSR_MIE_MSIE_RST_VAL;
    end else if (csr_mie_upd) begin
        csr_mie_stie_ff <= csr_w_data[SCR1_CSR_MIE_STIE_OFFSET];
        csr_mie_mtie_ff <= csr_w_data[SCR1_CSR_MIE_MTIE_OFFSET];
        csr_mie_seie_ff <= csr_w_data[SCR1_CSR_MIE_SEIE_OFFSET];
        csr_mie_meie_ff <= csr_w_data[SCR1_CSR_MIE_MEIE_OFFSET];
        csr_mie_ssie_ff <= csr_w_data[SCR1_CSR_MIE_SSIE_OFFSET];
        csr_mie_msie_ff <= csr_w_data[SCR1_CSR_MIE_MSIE_OFFSET];
	end else if (csr_sie_upd) begin
        csr_mie_stie_ff <= csr_w_data[SCR1_CSR_MIE_STIE_OFFSET];
        csr_mie_seie_ff <= csr_w_data[SCR1_CSR_MIE_SEIE_OFFSET];
        csr_mie_ssie_ff <= csr_w_data[SCR1_CSR_MIE_SSIE_OFFSET];
	end
end

always_comb begin
    csr_mie                           = '0;
    csr_mie[SCR1_CSR_MIE_SSIE_OFFSET] = csr_mie_ssie_ff;
    csr_mie[SCR1_CSR_MIE_MSIE_OFFSET] = csr_mie_msie_ff;
    csr_mie[SCR1_CSR_MIE_STIE_OFFSET] = csr_mie_stie_ff;
    csr_mie[SCR1_CSR_MIE_MTIE_OFFSET] = csr_mie_mtie_ff;
    csr_mie[SCR1_CSR_MIE_SEIE_OFFSET] = csr_mie_seie_ff;
    csr_mie[SCR1_CSR_MIE_MEIE_OFFSET] = csr_mie_meie_ff;
end

// MTVEC register
//------------------------------------------------------------------------------
// Holds trap vector configuation. Consists of base and mode parts

// MTVEC BASE part
//------------------------------------------------------------------------------
// Holds trap vector base address
generate
    // All bits of MTVEC base are Read-Only and hardwired to 0's
    if (SCR1_MTVEC_BASE_WR_BITS == 0) begin : mtvec_base_ro

        assign csr_mtvec_base   = SCR1_CSR_MTVEC_BASE_RST_VAL;

    // All bits of MTVEC base are RW
    end else if (SCR1_MTVEC_BASE_WR_BITS == SCR1_CSR_MTVEC_BASE_VAL_BITS) begin : mtvec_base_rw

        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_mtvec_base  <= SCR1_CSR_MTVEC_BASE_RST_VAL;
            end else if (csr_mtvec_upd) begin
                csr_mtvec_base  <= csr_w_data[`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS];
            end
        end

    // Lower bits of MTVEC base are RO, higher - RW
    end else begin : mtvec_base_ro_rw

        logic [(`SCR1_XLEN-1):(`SCR1_XLEN-SCR1_MTVEC_BASE_WR_BITS)]   csr_mtvec_base_reg;

        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_mtvec_base_reg <= SCR1_CSR_MTVEC_BASE_RST_VAL[(`SCR1_XLEN-1)-:SCR1_MTVEC_BASE_WR_BITS] ;
            end else if (csr_mtvec_upd) begin
                csr_mtvec_base_reg <= csr_w_data[(`SCR1_XLEN-1)-:SCR1_MTVEC_BASE_WR_BITS];
            end
        end

        assign csr_mtvec_base = {csr_mtvec_base_reg, SCR1_CSR_MTVEC_BASE_RST_VAL[SCR1_CSR_MTVEC_BASE_ZERO_BITS+:SCR1_CSR_MTVEC_BASE_RO_BITS]};
    end
endgenerate

// MTVEC MODE part
//------------------------------------------------------------------------------
// Chooses between direct (all exceptions set PC to BASE) or vectored
// (asynchronous interrupts set PC to BASE+4xcause) interrupt modes

`ifdef SCR1_MTVEC_MODE_EN
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtvec_mode_ff <= SCR1_CSR_MTVEC_MODE_DIRECT;
    end else if (csr_mtvec_upd) begin
        csr_mtvec_mode_ff <= csr_w_data[0];
    end
end

assign csr_mtvec_mode      = csr_mtvec_mode_ff;
assign csr_mtvec_mode_vect = (csr_mtvec_mode_ff == SCR1_CSR_MTVEC_MODE_VECTORED);
`else // SCR1_MTVEC_MODE_EN
assign csr_mtvec_mode = SCR1_CSR_MTVEC_MODE_DIRECT;
`endif // SCR1_MTVEC_MODE_EN

//------------------------------------------------------------------------------
// Machine Trap Handling registers
//------------------------------------------------------------------------------


// MSCRATCH register
//------------------------------------------------------------------------------
// Holds a pointer to a machine-mode hart-local context space

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mscratch_ff <= '0;
    end else if (csr_mscratch_upd) begin
        csr_mscratch_ff <= csr_w_data;
    end
end

// MEPC register
//------------------------------------------------------------------------------
// When a trap is taken into M-mode saves the virtual address of instruction that
// was interrupted or that encountered the exception

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mepc_ff <= '0;
    end else begin
        csr_mepc_ff <= csr_mepc_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc       : csr_mepc_next = exu2csr_pc_curr_i[`SCR1_XLEN-1:PC_LSB];
        e_irq_nmret : csr_mepc_next = exu2csr_pc_next_i[`SCR1_XLEN-1:PC_LSB];
        csr_mepc_upd: csr_mepc_next = csr_w_data[`SCR1_XLEN-1:PC_LSB];
        default     : csr_mepc_next = csr_mepc_ff;
    endcase
end

`ifdef SCR1_RVC_EXT
    assign csr_mepc = {csr_mepc_ff, 1'b0};
`else
    assign csr_mepc = {csr_mepc_ff, 2'b00};
`endif

// MCAUSE register
//------------------------------------------------------------------------------
// When a trap is taken into M-mode saves a code indicating the event that caused
// the trap

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mcause_i_ff  <= 1'b0;
        csr_mcause_ec_ff <= type_scr1_exc_code_e'(SCR1_EXC_CODE_RESET);
    end else begin
        csr_mcause_i_ff  <= csr_mcause_i_next;
        csr_mcause_ec_ff <= csr_mcause_ec_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc         : begin
            csr_mcause_i_next  = 1'b0;
            csr_mcause_ec_next = exu2csr_exc_code_i;
        end
        e_irq         : begin
            csr_mcause_i_next  = 1'b1;
            csr_mcause_ec_next = csr_mcause_ec_new;
        end
        csr_mcause_upd: begin
            csr_mcause_i_next  = csr_w_data[`SCR1_XLEN-1];
            csr_mcause_ec_next = type_scr1_exc_code_e'(csr_w_data[SCR1_EXC_CODE_WIDTH_E-1:0]);
        end
        default       : begin
            csr_mcause_i_next  = csr_mcause_i_ff;
            csr_mcause_ec_next = csr_mcause_ec_ff;
        end
    endcase
end

// MTVAL register
//------------------------------------------------------------------------------
// When a trap is taken into M-mode is either set to zero or written with exception-
// specific information

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtval_ff <= '0;
    end else begin
        csr_mtval_ff <= csr_mtval_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc        : csr_mtval_next = exu2csr_trap_val_i;
        e_irq        : csr_mtval_next = '0;
        csr_mtval_upd: csr_mtval_next = csr_w_data;
        default      : csr_mtval_next = csr_mtval_ff;
    endcase
end

// MIP register
//------------------------------------------------------------------------------
// Contains information on pending interrupts (external, software, timer IRQs)

always_ff @(posedge clk, negedge rst_n) begin
	if (~rst_n) begin
		csr_mip_ff	<= '0;
	end
	else begin
		csr_mip_ff	<= csr_mip_next;
	end
end

always_comb begin
    csr_mip_next                           = csr_mip_ff;

	case (1'b1)
		csr_mip_upd				: csr_mip_next	= csr_w_data;
		csr_sip_upd				: csr_mip_next	= csr_w_data;
		soc2csr_irq_mtimer_i	: begin
			csr_mip_next							= csr_mip_ff;
			csr_mip_next[SCR1_CSR_MIE_MTIE_OFFSET]	= 1'b1;
			csr_mip_next[SCR1_CSR_MIE_STIE_OFFSET]	= 1'b1;
		end
		soc2csr_irq_ext_i		: begin
			csr_mip_next							= csr_mip_ff;
			csr_mip_next[SCR1_CSR_MIE_MEIE_OFFSET]	= 1'b1;
			csr_mip_next[SCR1_CSR_MIE_SEIE_OFFSET]	= 1'b1;
		end
		soc2csr_irq_soft_i		: begin
			csr_mip_next							= csr_mip_ff;
			csr_mip_next[SCR1_CSR_MIE_MSIE_OFFSET]	= 1'b1;
			csr_mip_next[SCR1_CSR_MIE_SSIE_OFFSET]	= 1'b1;
		end
	endcase
end

assign csr_mip_mtip = csr_mip_ff[SCR1_CSR_MIE_MTIE_OFFSET];
assign csr_mip_meip = csr_mip_ff[SCR1_CSR_MIE_MEIE_OFFSET];
assign csr_mip_msip = csr_mip_ff[SCR1_CSR_MIE_MSIE_OFFSET];

assign csr_mip_stip = csr_mip_ff[SCR1_CSR_MIE_STIE_OFFSET];
assign csr_mip_seip = csr_mip_ff[SCR1_CSR_MIE_SEIE_OFFSET];
assign csr_mip_ssip = csr_mip_ff[SCR1_CSR_MIE_SSIE_OFFSET];

/*
assign csr_mip_mtip = soc2csr_irq_mtimer_i;
assign csr_mip_meip = soc2csr_irq_ext_i;
assign csr_mip_msip = soc2csr_irq_soft_i;

assign csr_mip_stip = soc2csr_irq_mtimer_i;
assign csr_mip_seip = soc2csr_irq_ext_i;
assign csr_mip_ssip = soc2csr_irq_soft_i;

always_comb begin
    csr_mip                           = '0;
    csr_mip[SCR1_CSR_MIE_SSIE_OFFSET] = csr_mip_ssip;
    csr_mip[SCR1_CSR_MIE_MSIE_OFFSET] = csr_mip_msip;
    csr_mip[SCR1_CSR_MIE_STIE_OFFSET] = csr_mip_stip;
    csr_mip[SCR1_CSR_MIE_MTIE_OFFSET] = csr_mip_mtip;
    csr_mip[SCR1_CSR_MIE_SEIE_OFFSET] = csr_mip_seip;
    csr_mip[SCR1_CSR_MIE_MEIE_OFFSET] = csr_mip_meip;
end
*/

//------------------------------------------------------------------------------
// Supervisor Trap Setup registers
//------------------------------------------------------------------------------

// SSTATUS register
//------------------------------------------------------------------------------
// STATUS is subset of MSTATUS

assign csr_sstatus_sie_ff	= csr_mstatus_sie_ff;
assign csr_sstatus_spie_ff	= csr_mstatus_spie_ff;
assign csr_sstatus_spp_ff	= csr_mstatus_spp_ff;
assign csr_sstatus_fs_ff	= csr_mstatus_fs_ff;
assign csr_sstatus_sum_ff	= csr_mstatus_sum_ff;
assign csr_sstatus_mxr_ff	= csr_mstatus_mxr_ff;

always_comb begin
    csr_sstatus                                                            	= '0;
    csr_sstatus[SCR1_CSR_SSTATUS_SIE_OFFSET]                               	= csr_sstatus_sie_ff;
    csr_sstatus[SCR1_CSR_SSTATUS_SPIE_OFFSET]                              	= csr_sstatus_spie_ff;
    csr_sstatus[SCR1_CSR_SSTATUS_SPP_OFFSET+1:SCR1_CSR_MSTATUS_SPP_OFFSET] 	= csr_sstatus_spp_ff;
	csr_sstatus[SCR1_CSR_SSTATUS_FS_OFFSET+:2]								= csr_sstatus_fs_ff;
	csr_sstatus[SCR1_CSR_SSTATUS_SUM_OFFSET]								= csr_sstatus_sum_ff;
	csr_sstatus[SCR1_CSR_SSTATUS_MXR_OFFSET]								= csr_sstatus_mxr_ff;
	csr_sstatus[SCR1_CSR_SSTATUS_UXL_OFFSET+:2]								= SCR1_MISA_MXL_64;
end


// SIE register
//------------------------------------------------------------------------------
// Contains interrupt enable bits (external, software, timer IRQs)
// SIE is subset of MIE (transparent only when delegation is on)

assign csr_sie_ssie_ff	= csr_mideleg_ssi & csr_mie_ssie_ff;
assign csr_sie_stie_ff	= csr_mideleg_sti & csr_mie_stie_ff;
assign csr_sie_seie_ff	= csr_mideleg_sei & csr_mie_seie_ff;

always_comb begin
    csr_sie                           = '0;
    csr_sie[SCR1_CSR_MIE_SSIE_OFFSET] = csr_sie_ssie_ff;
    csr_sie[SCR1_CSR_MIE_STIE_OFFSET] = csr_sie_stie_ff;
    csr_sie[SCR1_CSR_MIE_SEIE_OFFSET] = csr_sie_seie_ff;
end


// STVEC register
//------------------------------------------------------------------------------
// Holds trap vector configuation. Consists of base and mode parts

// STVEC BASE part
//------------------------------------------------------------------------------
// Holds trap vector base address
generate
    // All bits of STVEC base are Read-Only and hardwired to 0's
    if (SCR1_MTVEC_BASE_WR_BITS == 0) begin : stvec_base_ro

        assign csr_stvec_base   = SCR1_CSR_STVEC_BASE_RST_VAL;

    // All bits of STVEC base are RW
    end else if (SCR1_STVEC_BASE_WR_BITS == SCR1_CSR_STVEC_BASE_VAL_BITS) begin : stvec_base_rw

        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_stvec_base  <= SCR1_CSR_STVEC_BASE_RST_VAL;
            end else if (csr_stvec_upd) begin
                csr_stvec_base  <= csr_w_data[`SCR1_XLEN-1:SCR1_CSR_STVEC_BASE_ZERO_BITS];
            end
        end

    // Lower bits of STVEC base are RO, higher - RW
    end else begin : stvec_base_ro_rw

        logic [(`SCR1_XLEN-1):(`SCR1_XLEN-SCR1_STVEC_BASE_WR_BITS)]   csr_stvec_base_reg;

        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_stvec_base_reg <= SCR1_CSR_STVEC_BASE_RST_VAL[(`SCR1_XLEN-1)-:SCR1_STVEC_BASE_WR_BITS] ;
            end else if (csr_stvec_upd) begin
                csr_stvec_base_reg <= csr_w_data[(`SCR1_XLEN-1)-:SCR1_STVEC_BASE_WR_BITS];
            end
        end

        assign csr_stvec_base = {csr_stvec_base_reg, SCR1_CSR_STVEC_BASE_RST_VAL[SCR1_CSR_STVEC_BASE_ZERO_BITS+:SCR1_CSR_STVEC_BASE_RO_BITS]};
    end
endgenerate

// STVEC MODE part
//------------------------------------------------------------------------------
// Chooses between direct (all exceptions set PC to BASE) or vectored
// (asynchronous interrupts set PC to BASE+4xcause) interrupt modes

`ifdef SCR1_STVEC_MODE_EN
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_stvec_mode_ff <= SCR1_CSR_STVEC_MODE_DIRECT;
    end else if (csr_stvec_upd) begin
        csr_stvec_mode_ff <= csr_w_data[0];
    end
end

assign csr_stvec_mode      = csr_stvec_mode_ff;
assign csr_stvec_mode_vect = (csr_stvec_mode_ff == SCR1_CSR_STVEC_MODE_VECTORED);
`else // SCR1_STVEC_MODE_EN
assign csr_stvec_mode = SCR1_CSR_STVEC_MODE_DIRECT;
`endif // SCR1_STVEC_MODE_EN


//------------------------------------------------------------------------------
// Supervisor Trap Handling registers
//------------------------------------------------------------------------------

// SSCRATCH register
//------------------------------------------------------------------------------
// Holds a pointer to a S-mode hart-local context space

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_sscratch_ff <= '0;
    end else if (csr_sscratch_upd) begin
        csr_sscratch_ff <= csr_w_data;
    end
end

// SEPC register
//------------------------------------------------------------------------------
// When a trap is taken into S-mode saves the virtual address of instruction that
// was interrupted or that encountered the exception

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_sepc_ff <= '0;
    end else begin
        csr_sepc_ff <= csr_sepc_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc_s     : csr_sepc_next = exu2csr_pc_curr_i[`SCR1_XLEN-1:PC_LSB];
        e_irq_nsret : csr_sepc_next = exu2csr_pc_next_i[`SCR1_XLEN-1:PC_LSB];
        csr_sepc_upd: csr_sepc_next = csr_w_data[`SCR1_XLEN-1:PC_LSB];
        default     : csr_sepc_next = csr_sepc_ff;
    endcase
end

`ifdef SCR1_RVC_EXT
    assign csr_sepc = {csr_sepc_ff, 1'b0};
`else
    assign csr_sepc = {csr_sepc_ff, 2'b00};
`endif

// SCAUSE register
//------------------------------------------------------------------------------
// When a trap is taken into S-mode saves a code indicating the event that caused
// the trap

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_scause_i_ff  <= 1'b0;
        csr_scause_ec_ff <= type_scr1_exc_code_e'(SCR1_EXC_CODE_RESET);
    end else begin
        csr_scause_i_ff  <= csr_scause_i_next;
        csr_scause_ec_ff <= csr_scause_ec_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc_s       : begin
            csr_scause_i_next  = 1'b0;
            csr_scause_ec_next = exu2csr_exc_code_i;
        end
        e_irq_s       : begin
            csr_scause_i_next  = 1'b1;
            csr_scause_ec_next = csr_scause_ec_new;
        end
        csr_scause_upd: begin
            csr_scause_i_next  = csr_w_data[`SCR1_XLEN-1];
            csr_scause_ec_next = type_scr1_exc_code_e'(csr_w_data[SCR1_EXC_CODE_WIDTH_E-1:0]);
        end
        default       : begin
            csr_scause_i_next  = csr_scause_i_ff;
            csr_scause_ec_next = csr_scause_ec_ff;
        end
    endcase
end

// STVAL register
//------------------------------------------------------------------------------
// When a trap is taken into S-mode is either set to zero or written with exception-
// specific information

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_stval_ff <= '0;
    end else begin
        csr_stval_ff <= csr_stval_next;
    end
end

always_comb begin
    case (1'b1)
        e_exc_s      : csr_stval_next = exu2csr_trap_val_i;
        e_irq_s      : csr_stval_next = '0;
        csr_stval_upd: csr_stval_next = csr_w_data;
        default      : csr_stval_next = csr_stval_ff;
    endcase
end

// SIP register
//------------------------------------------------------------------------------
// Contains information on pending interrupts (external, software, timer IRQs)
// SIP is subset of MIP (transparent only when delegation is on)

assign csr_sip_stip = csr_mideleg_sti & csr_mip_ff[SCR1_CSR_MIE_STIE_OFFSET];
assign csr_sip_seip = csr_mideleg_sei & csr_mip_ff[SCR1_CSR_MIE_SEIE_OFFSET];
assign csr_sip_ssip = csr_mideleg_ssi & csr_mip_ff[SCR1_CSR_MIE_SSIE_OFFSET];

always_comb begin
	csr_sip								= '0;

	csr_sip[SCR1_CSR_MIE_STIE_OFFSET]	= csr_sip_stip;
	csr_sip[SCR1_CSR_MIE_SEIE_OFFSET]	= csr_sip_seip;
	csr_sip[SCR1_CSR_MIE_SSIE_OFFSET]	= csr_sip_ssip;
end


//------------------------------------------------------------------------------
// Supervisor Protection and Translation 
//------------------------------------------------------------------------------

// SATP register
//------------------------------------------------------------------------------
// Controls supervisor-mode address translation and protection

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_satp_ff <= '0;
    end else if (csr_satp_upd) begin
        csr_satp_ff <= csr_w_data;
    end
end

assign csr_satp_ppn		= csr_satp_ff[43:0];
assign csr_satp_asid	= csr_satp_ff[59:44];
assign csr_satp_mode	= csr_satp_ff[63:60];

assign satp_translation_on		= ((csr_satp_mode == 4'd8) 
								| (csr_satp_mode == 4'd9) 
								| (csr_satp_mode == 4'd10));

assign instr_translation_on		= satp_translation_on
							 	& (priv_u | priv_s);

assign ldst_translation_mprv_0	= satp_translation_on
							 	& (priv_u | priv_s);
assign ldst_translation_mprv_1	= satp_translation_on
								& ((csr_mstatus_mpp_ff == PRIV_U) 
								| (csr_mstatus_mpp_ff == PRIV_S));
assign ldst_translation_on		= (csr_mstatus_mprv_ff)	? ldst_translation_mprv_1
								: ldst_translation_mprv_0;


assign csr2mmu_trans_instr_o	= instr_translation_on;
assign csr2mmu_trans_ldst_o		= ldst_translation_on;

assign csr2mmu_priv_instr_o		= priv_curr;
assign csr2mmu_priv_ldst_o		= (csr_mstatus_mprv_ff) ? csr_mstatus_mpp_ff
								: priv_curr;

assign csr2mmu_sum_o			= csr_mstatus_sum_ff;
assign csr2mmu_mxr_o			= csr_mstatus_mxr_ff;
assign csr2mmu_ppn_o			= csr_satp_ppn;
assign csr2mmu_asid_o			= csr_satp_asid;

assign csr2mmu_asid_to_be_flushed_o		= 1'b0;
assign csr2mmu_vaddr_to_be_flushed_o	= 1'b0;

//------------------------------------------------------------------------------
// Machine Counters/Timers registers
//------------------------------------------------------------------------------
//
 // Registers:
 // - MCYCLE
 // - MINSTRET
//

`ifndef SCR1_CSR_REDUCED_CNT
// MCYCLE register
//------------------------------------------------------------------------------
// Holds the number of clock cycles since some arbitrary point of time in the
// past at which MCYCLE was zero

assign csr_mcycle_lo_inc = 1'b1
 `ifdef SCR1_MCOUNTEN_EN
                         & csr_mcounten_cy_ff
 `endif // SCR1_MCOUNTEN_EN
                         ;
assign csr_mcycle_hi_inc = csr_mcycle_lo_inc & (&csr_mcycle_lo_ff);

assign csr_mcycle_lo_upd = csr_mcycle_lo_inc | csr_mcycle_upd[0];
assign csr_mcycle_hi_upd = csr_mcycle_hi_inc | (|csr_mcycle_upd);

 `ifndef SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk) begin
 `else // SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk_alw_on) begin
 `endif // SCR1_CLKCTRL_EN
    if (~rst_n) begin
        csr_mcycle_lo_ff <= '0;
        csr_mcycle_hi_ff <= '0;
    end else begin
        if (csr_mcycle_lo_upd) csr_mcycle_lo_ff <= csr_mcycle_lo_next;
        if (csr_mcycle_hi_upd) csr_mcycle_hi_ff <= csr_mcycle_hi_next;
    end
end

assign csr_mcycle_hi_new  = csr_mcycle_hi_ff + 1'b1;

assign csr_mcycle_lo_next = csr_mcycle_upd[0] ? csr_w_data[7:0]
                          : csr_mcycle_lo_inc ? csr_mcycle_lo_ff + 1'b1
                                              : csr_mcycle_lo_ff;
assign csr_mcycle_hi_next = csr_mcycle_upd[0] ? {csr_mcycle_hi_new[63:32], csr_w_data[31:8]}
                          : csr_mcycle_upd[1] ? {csr_w_data[63:32], csr_mcycle_hi_new[31:8]}
                          : csr_mcycle_hi_inc ? csr_mcycle_hi_new
                                              : csr_mcycle_hi_ff;

assign csr_mcycle = {csr_mcycle_hi_ff, csr_mcycle_lo_ff};

// MINSTRET register
//------------------------------------------------------------------------------
// Holds the number of instructions executed by the core from some arbitrary time
// in the past at which MINSTRET was equal to zero

assign csr_minstret_lo_inc = exu2csr_instret_no_exc_i
 `ifdef SCR1_MCOUNTEN_EN
                           & csr_mcounten_ir_ff
 `endif // SCR1_MCOUNTEN_EN
                           ;
assign csr_minstret_hi_inc = csr_minstret_lo_inc & (&csr_minstret_lo_ff);

assign csr_minstret_lo_upd = csr_minstret_lo_inc | csr_minstret_upd[0];
assign csr_minstret_hi_upd = csr_minstret_hi_inc | (|csr_minstret_upd);

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_minstret_lo_ff <= '0;
        csr_minstret_hi_ff <= '0;
    end else begin
        if (csr_minstret_lo_upd) csr_minstret_lo_ff <= csr_minstret_lo_next;
        if (csr_minstret_hi_upd) csr_minstret_hi_ff <= csr_minstret_hi_next;
    end
end

assign csr_minstret_hi_new  = csr_minstret_hi_ff + 1'b1;

assign csr_minstret_lo_next = csr_minstret_upd[0] ? csr_w_data[7:0]
                            : csr_minstret_lo_inc ? csr_minstret_lo_ff + 1'b1
                                                  : csr_minstret_lo_ff;
assign csr_minstret_hi_next = csr_minstret_upd[0] ? {csr_minstret_hi_new[63:32], csr_w_data[31:8]}
                            : csr_minstret_upd[1] ? {csr_w_data[63:32], csr_minstret_hi_new[31:8]}
                            : csr_minstret_hi_inc ? csr_minstret_hi_new
                                                  : csr_minstret_hi_ff;

assign csr_minstret = {csr_minstret_hi_ff, csr_minstret_lo_ff};
`endif // SCR1_CSR_REDUCED_CNT

//------------------------------------------------------------------------------
// Non-standard CSR
//------------------------------------------------------------------------------

`ifdef SCR1_MCOUNTEN_EN
// MCOUNTEN register
//------------------------------------------------------------------------------
// Holds Counters enable bits (CY - MCYCLE counter; IR - MINSTRET counter)

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mcounten_cy_ff <= 1'b1;
        csr_mcounten_ir_ff <= 1'b1;
    end else if (csr_mcounten_upd) begin
        csr_mcounten_cy_ff <= csr_w_data[SCR1_CSR_MCOUNTEN_CY_OFFSET];
        csr_mcounten_ir_ff <= csr_w_data[SCR1_CSR_MCOUNTEN_IR_OFFSET];
    end
end

always_comb begin
    csr_mcounten    = '0;
    csr_mcounten[SCR1_CSR_MCOUNTEN_CY_OFFSET]   = csr_mcounten_cy_ff;
    csr_mcounten[SCR1_CSR_MCOUNTEN_IR_OFFSET]   = csr_mcounten_ir_ff;
end
`endif // SCR1_MCOUNTEN_EN

//------------------------------------------------------------------------------
// CSR <-> EXU interface
//------------------------------------------------------------------------------

// CSR exception
assign csr2exu_rw_exc_o = csr_r_exc | csr_w_exc
`ifdef SCR1_DBG_EN
                        | (csr2hdu_req_o & (hdu2csr_resp_i != SCR1_CSR_RESP_OK))
`endif // SCR1_DBG_EN
`ifdef SCR1_TDU_EN
                        | (csr2tdu_req_o & (tdu2csr_resp_i != SCR1_CSR_RESP_OK))
`endif // SCR1_TDU_EN
                        ;
assign csr2exu_irq_o    = ((csr_eirq_m_pnd_en 	| csr_sirq_m_pnd_en 	| csr_tirq_m_pnd_en)
						| (csr_eirq_s_pnd_en 	| csr_sirq_s_pnd_en 	| csr_tirq_s_pnd_en)
						| (csr_eirq_s_de_pnd_en	| csr_sirq_s_de_pnd_en 	| csr_tirq_s_de_pnd_en)) 
						& csr_mstatus_mie_ff;

assign csr2exu_mstatus_mie_up_o = csr_mstatus_upd | csr_mie_upd | e_mret;
assign csr2exu_sstatus_sie_up_o = csr_sstatus_upd | csr_sie_upd | e_sret;

// New PC multiplexer
`ifndef SCR1_MTVEC_MODE_EN
assign csr2exu_new_pc_o = (exu2csr_mret_instr_i & ~exu2csr_take_irq_i)
                        ? csr_mepc
                        : (exu2csr_sret_instr_i & ~exu2csr_take_irq_i)
						? csr_sepc
						: csr_mtvec_base;
`else // SCR1_MTVEC_MODE_EN
always_comb begin
    if (exu2csr_mret_instr_i & ~exu2csr_take_irq_i) begin
        csr2exu_new_pc_o  = csr_mepc;
    end 
	else if (exu2csr_sret_instr_i & ~exu2csr_take_irq_i) begin
		csr2exu_new_pc_o  = csr_sepc;
	end
	else if (~exc_delegated & ~irq_delegated) begin
        if (csr_mtvec_mode_vect) begin
            case (1'b1)
                exu2csr_take_exc_i	: csr2exu_new_pc_o = {csr_mtvec_base};
                csr_eirq_m_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_M_EXTERNAL, 2'd0};
                csr_sirq_m_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_M_SOFTWARE, 2'd0};
                csr_tirq_m_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_M_TIMER, 2'd0};
                csr_eirq_s_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_EXTERNAL, 2'd0};
                csr_sirq_s_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_SOFTWARE, 2'd0};
                csr_tirq_s_pnd_en	: csr2exu_new_pc_o = {csr_mtvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_TIMER, 2'd0};
                default           	: csr2exu_new_pc_o = {csr_mtvec_base};
            endcase
        end else begin // direct mode
            csr2exu_new_pc_o = csr_mtvec_base;
        end
    end
	else begin
        if (csr_stvec_mode_vect) begin
            case (1'b1)
                exu2csr_take_exc_i		: csr2exu_new_pc_o = {csr_stvec_base};
                csr_eirq_s_de_pnd_en	: csr2exu_new_pc_o = {csr_stvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_EXTERNAL, 2'd0};
                csr_sirq_s_de_pnd_en	: csr2exu_new_pc_o = {csr_stvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_SOFTWARE, 2'd0};
                csr_tirq_s_de_pnd_en	: csr2exu_new_pc_o = {csr_stvec_base[`SCR1_XLEN-1:7], SCR1_EXC_CODE_IRQ_S_TIMER, 2'd0};
                default           		: csr2exu_new_pc_o = {csr_stvec_base};
            endcase
        end else begin // direct mode
            csr2exu_new_pc_o = csr_stvec_base;
        end
    end
end
`endif // SCR1_MTVEC_MODE_EN

`ifdef SCR1_IPIC_EN
//------------------------------------------------------------------------------
// CSR <-> IPIC interface
//------------------------------------------------------------------------------

assign csr_ipic_req     = csr2ipic_r_req_o | csr2ipic_w_req_o;
assign csr2ipic_addr_o  = csr_ipic_req     ? exu2csr_rw_addr_i[2:0] : '0;
assign csr2ipic_wdata_o = csr2ipic_w_req_o ? exu2csr_w_data_i       : '0;
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBG_EN
//------------------------------------------------------------------------------
// CSR <-> HDU interface
//------------------------------------------------------------------------------

assign csr2hdu_req_o   = csr_hdu_req & exu_req_no_exc;
assign csr2hdu_cmd_o   = exu2csr_w_cmd_i;
assign csr2hdu_addr_o  = exu2csr_rw_addr_i[SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0];
assign csr2hdu_wdata_o = exu2csr_w_data_i;
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
//------------------------------------------------------------------------------
// CSR <-> TDU interface
//------------------------------------------------------------------------------

assign csr2tdu_req_o   = csr_brkm_req & exu_req_no_exc;
assign csr2tdu_cmd_o   = exu2csr_w_cmd_i;
assign csr2tdu_addr_o  = exu2csr_rw_addr_i[SCR1_CSR_ADDR_TDU_OFFS_W-1:0];
assign csr2tdu_wdata_o = exu2csr_w_data_i;
`endif // SCR1_TDU_EN

`ifdef SCR1_TRGT_SIMULATION
//------------------------------------------------------------------------------
// Assertions
//------------------------------------------------------------------------------

// X checks

SCR1_SVA_CSR_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2csr_r_req_i, exu2csr_w_req_i, exu2csr_take_irq_i, exu2csr_take_exc_i, exu2csr_mret_update_i
`ifndef SCR1_CSR_REDUCED_CNT
    , exu2csr_instret_no_exc_i
`endif // SCR1_CSR_REDUCED_CNT
    })
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_READ : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_r_req_i |-> !$isunknown({exu2csr_rw_addr_i, csr2exu_r_data_o, csr2exu_rw_exc_o})
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_WRITE : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_w_req_i |-> !$isunknown({exu2csr_rw_addr_i, exu2csr_w_cmd_i, exu2csr_w_data_i, csr2exu_rw_exc_o})
    ) else $error("CSR Error: unknown control values");

`ifdef SCR1_IPIC_EN
SCR1_SVA_CSR_XCHECK_READ_IPIC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2ipic_r_req_o |-> !$isunknown({csr2ipic_addr_o, ipic2csr_rdata_i})
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_WRITE_IPIC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2ipic_w_req_o |-> !$isunknown({csr2ipic_addr_o, csr2ipic_wdata_o})
    ) else $error("CSR Error: unknown control values");
`endif // SCR1_IPIC_EN

// Behavior checks

SCR1_SVA_CSR_MRET : assert property (
    @(negedge clk) disable iff (~rst_n)
    e_mret |=> ($stable(csr_mepc_ff) & $stable(csr_mtval_ff))
    ) else $error("CSR Error: MRET wrong behavior");

SCR1_SVA_CSR_MRET_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_mret_instr_i & e_irq)
    |=> ($stable(csr_mepc_ff) & (exu2csr_pc_curr_i != csr_mepc))
    ) else $error("CSR Error: MRET+IRQ wrong behavior");

SCR1_SVA_CSR_EXC_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_take_exc_i & exu2csr_take_irq_i
`ifdef SCR1_DBG_EN
    & ~hdu2csr_no_commit_i
`endif
    ) |=>
    (~csr_mstatus_mie_ff & (~csr_mcause_i_ff)
    & (exu2csr_pc_curr_i=={csr_mtvec_base}))
    ) else $error("CSR Error: wrong EXC+IRQ");

SCR1_SVA_CSR_EVENTS : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({e_irq, e_exc, e_mret})
    ) else $error("CSR Error: more than one event at a time");

SCR1_SVA_CSR_RW_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2exu_rw_exc_o |-> (exu2csr_w_req_i | exu2csr_r_req_i)
    ) else $error("CSR Error: impossible exception");

SCR1_SVA_CSR_MSTATUS_MIE_UP : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2exu_mstatus_mie_up_o |=> ~csr2exu_mstatus_mie_up_o
    ) else $error("CSR Error: csr2exu_mstatus_mie_up_o can only be high for one mcycle");


`ifndef SCR1_CSR_REDUCED_CNT

SCR1_SVA_CSR_CYCLE_INC : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    (~|csr_mcycle_upd) |=>
`ifdef SCR1_MCOUNTEN_EN
    ($past(csr_mcounten_cy_ff) ? (csr_mcycle == $past(csr_mcycle + 1'b1)) : $stable(csr_mcycle))
`else //SCR1_MCOUNTEN_EN
    (csr_mcycle == $past(csr_mcycle + 1'b1))
`endif // SCR1_MCOUNTEN_EN
    ) else $error("CSR Error: CYCLE increment wrong behavior");

SCR1_SVA_CSR_INSTRET_INC : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_instret_no_exc_i & ~|csr_minstret_upd) |=>
`ifdef SCR1_MCOUNTEN_EN
    ($past(csr_mcounten_ir_ff) ? (csr_minstret == $past(csr_minstret + 1'b1)) : $stable(csr_minstret))
`else //SCR1_MCOUNTEN_EN
    (csr_minstret == $past(csr_minstret + 1'b1))
`endif // SCR1_MCOUNTEN_EN
    ) else $error("CSR Error: INSTRET increment wrong behavior");

SCR1_SVA_CSR_CYCLE_INSTRET_UP : assert property (
    @(negedge clk) disable iff (~rst_n)
    ~(&csr_minstret_upd | &csr_mcycle_upd)
    ) else $error("CSR Error: INSTRET/CYCLE up illegal value");

`endif // SCR1_CSR_REDUCED_CNT

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_csr
