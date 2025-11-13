/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_arch_types.svh>
/// @brief      Pipeline types description file
///

`ifndef SCR1_ARCH_TYPES_SVH
`define SCR1_ARCH_TYPES_SVH

`include "scr1_arch_description.svh"

//-------------------------------------------------------------------------------
// RF and CSR parameters
//-------------------------------------------------------------------------------

`ifdef SCR1_RVE_EXT
  `define SCR1_MPRF_AWIDTH    4
  `define SCR1_MPRF_SIZE      16
`else // SCR1_RVE_EXT
  `define SCR1_MPRF_AWIDTH    5
  `define SCR1_MPRF_SIZE      32
`endif // SCR1_RVE_EXT

  `define SCR1_FPRF_AWIDTH    5
  `define SCR1_FPRF_SIZE      32

typedef logic [`SCR1_XLEN-1:0]  type_scr1_mprf_v;
typedef logic [`SCR1_XLEN-1:0]  type_scr1_fprf_v;
typedef logic [`SCR1_XLEN-1:0]  type_scr1_pc_v;

parameter int unsigned  SCR1_CSR_ADDR_WIDTH             = 12;
parameter int unsigned  SCR1_CSR_MTVEC_BASE_ZERO_BITS   = 0;
parameter int unsigned  SCR1_CSR_MTVEC_BASE_VAL_BITS    = `SCR1_XLEN-SCR1_CSR_MTVEC_BASE_ZERO_BITS;
parameter bit [`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS]  SCR1_CSR_MTVEC_BASE_WR_RST_VAL    =
                                      SCR1_CSR_MTVEC_BASE_VAL_BITS'(SCR1_ARCH_MTVEC_BASE >> SCR1_CSR_MTVEC_BASE_ZERO_BITS);
parameter int unsigned  SCR1_CSR_MTVEC_BASE_RO_BITS = (`SCR1_XLEN-(SCR1_CSR_MTVEC_BASE_ZERO_BITS+SCR1_MTVEC_BASE_WR_BITS));

parameter int unsigned  SCR1_CSR_STVEC_BASE_ZERO_BITS   = 0;
parameter int unsigned  SCR1_CSR_STVEC_BASE_VAL_BITS    = `SCR1_XLEN-SCR1_CSR_STVEC_BASE_ZERO_BITS;
parameter bit [`SCR1_XLEN-1:SCR1_CSR_STVEC_BASE_ZERO_BITS]  SCR1_CSR_STVEC_BASE_WR_RST_VAL    =
                                      SCR1_CSR_STVEC_BASE_VAL_BITS'(SCR1_ARCH_STVEC_BASE >> SCR1_CSR_STVEC_BASE_ZERO_BITS);
parameter int unsigned  SCR1_CSR_STVEC_BASE_RO_BITS = (`SCR1_XLEN-(SCR1_CSR_STVEC_BASE_ZERO_BITS+SCR1_STVEC_BASE_WR_BITS));

//`define SCR1_MTVAL_ILLEGAL_INSTR_EN

//-------------------------------------------------------------------------------
// Exception and IRQ codes
//-------------------------------------------------------------------------------
parameter int unsigned SCR1_EXC_CODE_WIDTH_E    = 5;

// Exceptions
typedef enum logic [SCR1_EXC_CODE_WIDTH_E-1:0] {
    SCR1_EXC_CODE_INSTR_MISALIGN        	= 5'd0,     // from EXU
    SCR1_EXC_CODE_INSTR_ACCESS_FAULT    	= 5'd1,     // from IFU
    SCR1_EXC_CODE_ILLEGAL_INSTR         	= 5'd2,     // from IDU or CSR
    SCR1_EXC_CODE_BREAKPOINT            	= 5'd3,     // from IDU or BRKM
    SCR1_EXC_CODE_LD_ADDR_MISALIGN      	= 5'd4,     // from LSU
    SCR1_EXC_CODE_LD_ACCESS_FAULT       	= 5'd5,     // from LSU
    SCR1_EXC_CODE_ST_ADDR_MISALIGN      	= 5'd6,     // from LSU
    SCR1_EXC_CODE_ST_ACCESS_FAULT       	= 5'd7,     // from LSU
	SCR1_EXC_CODE_ECALL_U					= 5'd8,
	SCR1_EXC_CODE_ECALL_S					= 5'd9,
    SCR1_EXC_CODE_ECALL_M               	= 5'd11,    // from IDU
	SCR1_EXC_CODE_INSTR_PAGE_FAULT			= 5'd12,
	SCR1_EXC_CODE_LD_PAGE_FAULT				= 5'd13,
	SCR1_EXC_CODE_ST_PAGE_FAULT				= 5'd15,
	SCR1_EXC_CODE_INSTR_GUEST_PAGE_FAULT	= 5'd20,
	SCR1_EXC_CODE_LD_GUEST_PAGE_FAULT		= 5'd21,
	SCR1_EXC_CODE_VIRTUAL_INSTR				= 5'd22,
	SCR1_EXC_CODE_ST_GUEST_PAGE_FAULT		= 5'd23,
	SCR1_EXC_CODE_DEBUG_REQ					= 5'd24
} type_scr1_exc_code_e;

// IRQs, reset
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_S_SOFTWARE      = 4'd1;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_SOFTWARE      = 4'd3;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_S_TIMER         = 4'd5;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_TIMER         = 4'd7;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_S_EXTERNAL      = 4'd9;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_EXTERNAL      = 4'd11;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_RESET               = 4'd0;

//-------------------------------------------------------------------------------
// Operand width for BRKM
//-------------------------------------------------------------------------------
typedef enum logic [1:0] {
    SCR1_OP_WIDTH_BYTE  = 2'b00,
    SCR1_OP_WIDTH_HALF  = 2'b01,
    SCR1_OP_WIDTH_WORD  = 2'b10
`ifdef SCR1_XPROP_EN
    ,
    SCR1_OP_WIDTH_ERROR = 'x
`endif // SCR1_XPROP_EN
} type_scr1_op_width_e;

`endif //SCR1_ARCH_TYPES_SVH
