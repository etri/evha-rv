/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_csr.svh>
/// @brief      CSR mapping/description file
///

`ifndef SCR1_CSR_SVH
`define SCR1_CSR_SVH

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_ipic.svh"

`ifdef SCR1_RVE_EXT
`define SCR1_CSR_REDUCED_CNT
`endif // SCR1_RVE_EXT

`ifdef SCR1_CSR_REDUCED_CNT
`undef SCR1_MCOUNTEN_EN
`endif // SCR1_CSR_REDUCED_CNT

//-------------------------------------------------------------------------------
// CSR addresses (standard)
//-------------------------------------------------------------------------------

// Floating-point (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_FFLAGS     	= SCR1_CSR_ADDR_WIDTH'('h001);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_FRM     		= SCR1_CSR_ADDR_WIDTH'('h002);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_FCSR     		= SCR1_CSR_ADDR_WIDTH'('h003);

// Machine Information Registers (read-only)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MVENDORID     = SCR1_CSR_ADDR_WIDTH'('hF11);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MARCHID       = SCR1_CSR_ADDR_WIDTH'('hF12);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MIMPID        = SCR1_CSR_ADDR_WIDTH'('hF13);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MHARTID       = SCR1_CSR_ADDR_WIDTH'('hF14);

// Machine Trap Setup (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MSTATUS       = SCR1_CSR_ADDR_WIDTH'('h300);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MISA          = SCR1_CSR_ADDR_WIDTH'('h301);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MEDELEG       = SCR1_CSR_ADDR_WIDTH'('h302);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MIDELEG       = SCR1_CSR_ADDR_WIDTH'('h303);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MIE           = SCR1_CSR_ADDR_WIDTH'('h304);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MTVEC         = SCR1_CSR_ADDR_WIDTH'('h305);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MCOUNTEREN    = SCR1_CSR_ADDR_WIDTH'('h306);

// Machine Trap Handling (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MSCRATCH      = SCR1_CSR_ADDR_WIDTH'('h340);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MEPC          = SCR1_CSR_ADDR_WIDTH'('h341);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MCAUSE        = SCR1_CSR_ADDR_WIDTH'('h342);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MTVAL         = SCR1_CSR_ADDR_WIDTH'('h343);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MIP           = SCR1_CSR_ADDR_WIDTH'('h344);

// Machine Counters/Timers (read-write)
`ifndef SCR1_CSR_REDUCED_CNT
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MCYCLE        = SCR1_CSR_ADDR_WIDTH'('hB00);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MINSTRET      = SCR1_CSR_ADDR_WIDTH'('hB02);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MCYCLEH       = SCR1_CSR_ADDR_WIDTH'('hB80);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MINSTRETH     = SCR1_CSR_ADDR_WIDTH'('hB82);
`endif // SCR1_CSR_REDUCED_CNT


// Supervisor Trap Setup (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SSTATUS       = SCR1_CSR_ADDR_WIDTH'('h100);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SIE           = SCR1_CSR_ADDR_WIDTH'('h104);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_STVEC         = SCR1_CSR_ADDR_WIDTH'('h105);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SCOUNTEREN    = SCR1_CSR_ADDR_WIDTH'('h106);

// Supervisor Trap Handlinsg (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SSCRATCH      = SCR1_CSR_ADDR_WIDTH'('h140);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SEPC          = SCR1_CSR_ADDR_WIDTH'('h141);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SCAUSE        = SCR1_CSR_ADDR_WIDTH'('h142);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_STVAL         = SCR1_CSR_ADDR_WIDTH'('h143);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_SIP           = SCR1_CSR_ADDR_WIDTH'('h144);

// Supervisor Protection and Translation (read-write)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0]	SCR1_CSR_ADDR_SATP			= SCR1_CSR_ADDR_WIDTH'('h180);


// Shadow Counters/Timers (read-only)
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TIME          = SCR1_CSR_ADDR_WIDTH'('hC01);
`ifndef SCR1_CSR_REDUCED_CNT
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_CYCLE         = SCR1_CSR_ADDR_WIDTH'('hC00);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_INSTRET       = SCR1_CSR_ADDR_WIDTH'('hC02);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TIMEH         = SCR1_CSR_ADDR_WIDTH'('hC81);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_CYCLEH        = SCR1_CSR_ADDR_WIDTH'('hC80);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_INSTRETH      = SCR1_CSR_ADDR_WIDTH'('hC82);
`endif // SCR1_CSR_REDUCED_CNT


`ifdef SCR1_DBG_EN
//parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_DBGC_SCRATCH  = 'h7C8;
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_HDU_MBASE    = SCR1_CSR_ADDR_WIDTH'('h7B0);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_HDU_MSPAN    = SCR1_CSR_ADDR_WIDTH'('h004);    // must be power of 2
`endif // SCR1_DBG_EN

//-------------------------------------------------------------------------------
// CSR addresses (non-standard)
//-------------------------------------------------------------------------------
`ifdef SCR1_MCOUNTEN_EN
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_MCOUNTEN      = SCR1_CSR_ADDR_WIDTH'('h7E0);
`endif // SCR1_MCOUNTEN_EN

`ifdef SCR1_TDU_EN
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_MBASE    = SCR1_CSR_ADDR_WIDTH'('h7A0);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_MSPAN    = SCR1_CSR_ADDR_WIDTH'('h008);    // must be power of 2
`endif // SCR1_TDU_EN

`ifdef SCR1_IPIC_EN
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_BASE     = SCR1_CSR_ADDR_WIDTH'('hBF0);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_CISV     = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_CISV );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_CICSR    = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_CICSR);
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_IPR      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_IPR  );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_ISVR     = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_ISVR );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_EOI      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_EOI  );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_SOI      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_SOI  );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_IDX      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_IDX  );
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_IPIC_ICSR     = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_ICSR );
`endif // SCR1_IPIC_EN


//-------------------------------------------------------------------------------
// Machine-level CSR definitions
//-------------------------------------------------------------------------------

// General
parameter bit [`SCR1_XLEN-1:0] SCR1_RST_VECTOR      = SCR1_ARCH_RST_VECTOR;

// Reset values
parameter bit 		SCR1_CSR_MIE_SSIE_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIE_MSIE_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIE_STIE_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIE_MTIE_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIE_SEIE_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIE_MEIE_RST_VAL       = 1'b0;

parameter bit 		SCR1_CSR_MIP_SSIP_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIP_MSIP_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIP_STIP_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIP_MTIP_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIP_SEIP_RST_VAL       = 1'b0;
parameter bit 		SCR1_CSR_MIP_MEIP_RST_VAL       = 1'b0;

parameter bit 		SCR1_CSR_MSTATUS_SIE_RST_VAL    = 1'b0;
parameter bit 		SCR1_CSR_MSTATUS_MIE_RST_VAL    = 1'b0;
parameter bit 		SCR1_CSR_MSTATUS_SPIE_RST_VAL   = 1'b1;
parameter bit 		SCR1_CSR_MSTATUS_MPIE_RST_VAL   = 1'b1;
parameter bit [1:0]	SCR1_CSR_MSTATUS_SPP_RST_VAL	= 2'b00;
parameter bit [1:0]	SCR1_CSR_MSTATUS_MPP_RST_VAL	= 2'b00;
parameter bit [1:0]	SCR1_CSR_MSTATUS_FS_RST_VAL		= 2'b00;

// MISA
`define SCR1_RVC_ENC                                `SCR1_XLEN'h00_0004
`define SCR1_RVE_ENC                                `SCR1_XLEN'h00_0010
`define SCR1_RVI_ENC                                `SCR1_XLEN'h00_0100
`define SCR1_RVM_ENC                                `SCR1_XLEN'h00_1000
`define SCR1_RVF_ENC								`SCR1_XLEN'h00_0020
`define SCR1_RVD_ENC								`SCR1_XLEN'h00_0008
`define SCR1_RVA_ENC								`SCR1_XLEN'h00_0001
`define SCR1_SMODE_ENC								`SCR1_XLEN'h04_0000
`define SCR1_UMODE_ENC								`SCR1_XLEN'h10_0000
parameter bit [1:0]             SCR1_MISA_MXL_32    = 2'd1;
parameter bit [1:0]             SCR1_MISA_MXL_64    = 2'd2;
parameter bit [`SCR1_XLEN-1:0]  SCR1_CSR_MISA       = (SCR1_MISA_MXL_64 << (`SCR1_XLEN-2))
`ifndef SCR1_RVE_EXT
                                                    | `SCR1_RVI_ENC
`else // SCR1_RVE_EXT
                                                    | `SCR1_RVE_ENC
`endif // SCR1_RVE_EXT
`ifdef SCR1_RVC_EXT
                                                    | `SCR1_RVC_ENC
`endif // SCR1_RVC_EXT
`ifdef SCR1_RVM_EXT
                                                    | `SCR1_RVM_ENC
`endif // SCR1_RVM_EXT
                                                    | `SCR1_RVF_ENC
                                                    | `SCR1_RVD_ENC
                                                    | `SCR1_RVA_ENC
													| `SCR1_SMODE_ENC
													| `SCR1_UMODE_ENC
                                                    ;

// MVENDORID
parameter bit [`SCR1_XLEN-1:0] SCR1_CSR_MVENDORID   = `SCR1_MVENDORID;

// MARCHID
parameter bit [`SCR1_XLEN-1:0] SCR1_CSR_MARCHID     = `SCR1_XLEN'd8;

// MIMPID
parameter bit [`SCR1_XLEN-1:0] SCR1_CSR_MIMPID      = `SCR1_MIMPID;

// MSTATUS
parameter bit [1:0] SCR1_CSR_MSTATUS_MPP            = 2'b11;
parameter int unsigned SCR1_CSR_MSTATUS_SIE_OFFSET	= 1;
parameter int unsigned SCR1_CSR_MSTATUS_MIE_OFFSET	= 3;
parameter int unsigned SCR1_CSR_MSTATUS_SPIE_OFFSET	= 5;
parameter int unsigned SCR1_CSR_MSTATUS_MPIE_OFFSET	= 7;
parameter int unsigned SCR1_CSR_MSTATUS_SPP_OFFSET 	= 8;
parameter int unsigned SCR1_CSR_MSTATUS_MPP_OFFSET	= 11;
parameter int unsigned SCR1_CSR_MSTATUS_FS_OFFSET	= 13;
parameter int unsigned SCR1_CSR_MSTATUS_MPRV_OFFSET	= 17;
parameter int unsigned SCR1_CSR_MSTATUS_SUM_OFFSET	= 18;
parameter int unsigned SCR1_CSR_MSTATUS_MXR_OFFSET	= 19;
parameter int unsigned SCR1_CSR_MSTATUS_TVM_OFFSET	= 20;
parameter int unsigned SCR1_CSR_MSTATUS_TSR_OFFSET	= 22;
parameter int unsigned SCR1_CSR_MSTATUS_UXL_OFFSET	= 32;
parameter int unsigned SCR1_CSR_MSTATUS_SXL_OFFSET	= 34;

// MTVEC
// bits [5:0] are always zero
parameter bit [`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS] SCR1_CSR_MTVEC_BASE_RST_VAL  = SCR1_CSR_MTVEC_BASE_WR_RST_VAL;

parameter bit SCR1_CSR_MTVEC_MODE_DIRECT            = 1'b0;
`ifdef SCR1_MTVEC_MODE_EN
parameter bit SCR1_CSR_MTVEC_MODE_VECTORED          = 1'b1;
`endif // SCR1_MTVEC_MODE_EN

// MIE, MIP
parameter int unsigned SCR1_CSR_MIE_SSIE_OFFSET     = 1;
parameter int unsigned SCR1_CSR_MIE_MSIE_OFFSET     = 3;
parameter int unsigned SCR1_CSR_MIE_STIE_OFFSET     = 5;
parameter int unsigned SCR1_CSR_MIE_MTIE_OFFSET     = 7;
parameter int unsigned SCR1_CSR_MIE_SEIE_OFFSET     = 9;
parameter int unsigned SCR1_CSR_MIE_MEIE_OFFSET     = 11;

`ifdef SCR1_MCOUNTEN_EN
// MCOUNTEN
parameter int unsigned SCR1_CSR_MCOUNTEN_CY_OFFSET  = 0;
parameter int unsigned SCR1_CSR_MCOUNTEN_IR_OFFSET  = 2;
`endif // SCR1_MCOUNTEN_EN

// MCAUSE
typedef logic [`SCR1_XLEN-2:0]      type_scr1_csr_mcause_ec_v;

// MCYCLE, MINSTRET
`ifdef SCR1_CSR_REDUCED_CNT
parameter int unsigned SCR1_CSR_COUNTERS_WIDTH      = 32;
`else // ~SCR1_CSR_REDUCED_CNT
parameter int unsigned SCR1_CSR_COUNTERS_WIDTH      = 64;
`endif // ~SCR1_CSR_REDUCED_CNT

// HPM
parameter bit [6:0] SCR1_CSR_ADDR_HPMCOUNTER_MASK   = 7'b1100000;
parameter bit [6:0] SCR1_CSR_ADDR_HPMCOUNTERH_MASK  = 7'b1100100;
parameter bit [6:0] SCR1_CSR_ADDR_MHPMCOUNTER_MASK  = 7'b1011000;
parameter bit [6:0] SCR1_CSR_ADDR_MHPMCOUNTERH_MASK = 7'b1011100;
parameter bit [6:0] SCR1_CSR_ADDR_MHPMEVENT_MASK    = 7'b0011001;


//-------------------------------------------------------------------------------
// Supervisor-level CSR definitions
//-------------------------------------------------------------------------------

// SSTATUS
parameter int unsigned SCR1_CSR_SSTATUS_SIE_OFFSET	= 1;
parameter int unsigned SCR1_CSR_SSTATUS_SPIE_OFFSET	= 5;
parameter int unsigned SCR1_CSR_SSTATUS_SPP_OFFSET 	= 8;
parameter int unsigned SCR1_CSR_SSTATUS_FS_OFFSET	= 13;
parameter int unsigned SCR1_CSR_SSTATUS_SUM_OFFSET	= 18;
parameter int unsigned SCR1_CSR_SSTATUS_MXR_OFFSET	= 19;
parameter int unsigned SCR1_CSR_SSTATUS_UXL_OFFSET	= 32;

// STVEC
// bits [5:0] are always zero
parameter bit [`SCR1_XLEN-1:SCR1_CSR_STVEC_BASE_ZERO_BITS] SCR1_CSR_STVEC_BASE_RST_VAL  = SCR1_CSR_STVEC_BASE_WR_RST_VAL;

parameter bit SCR1_CSR_STVEC_MODE_DIRECT            = 1'b0;
`ifdef SCR1_STVEC_MODE_EN
parameter bit SCR1_CSR_STVEC_MODE_VECTORED          = 1'b1;
`endif // SCR1_STVEC_MODE_EN


//-------------------------------------------------------------------------------
// MMU configuration
//-------------------------------------------------------------------------------

typedef struct packed {
	int unsigned XLEN;
	int unsigned VLEN;
	int unsigned PLEN;
	int unsigned GPLEN;
	bit IS_XLEN64;
	int unsigned ASID_WIDTH;
	int unsigned VMID_WIDTH;
	
	int unsigned NrPMPEntries;
	int unsigned PtLevels;
	int unsigned VpnLen;
	int unsigned InstrTlbEntries;
	int unsigned DataTlbEntries;
    bit unsigned UseSharedTlb;
    int unsigned SharedTlbDepth;

	bit          RVH;

	int unsigned PPNW;
	int unsigned GPPNW;
	int unsigned SV;

	bit          TvalEn;

	int unsigned ICACHE_INDEX_WIDTH;
	int unsigned ICACHE_TAG_WIDTH;
	int unsigned DCACHE_INDEX_WIDTH;
	int unsigned DCACHE_TAG_WIDTH;
	int unsigned DCACHE_USER_WIDTH;
	int unsigned DcacheIdWidth;
} cva6_cfg_t;


//-------------------------------------------------------------------------------
// Types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_CSR_RESP_OK,
    SCR1_CSR_RESP_ER
`ifdef SCR1_XPROP_EN
    ,
    SCR1_CSR_RESP_ERROR = 'x
`endif // SCR1_XPROP_EN
} type_scr1_csr_resp_e;

`endif // SCR1_CSR_SVH
