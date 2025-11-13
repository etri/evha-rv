/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_memif.svh>
/// @brief      Memory interface definitions file
///

`ifndef SCR1_MEMIF_SVH
`define SCR1_MEMIF_SVH

`include "scr1_arch_description.svh"

//-------------------------------------------------------------------------------
// Memory command enum
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_MEM_CMD_RD     = 1'b0,
    SCR1_MEM_CMD_WR     = 1'b1
`ifdef SCR1_XPROP_EN
    ,
    SCR1_MEM_CMD_ERROR  = 'x
`endif // SCR1_XPROP_EN
} type_scr1_mem_cmd_e;

//-------------------------------------------------------------------------------
// Memory data width enum
//-------------------------------------------------------------------------------
typedef enum logic[1:0] {
    SCR1_MEM_WIDTH_BYTE     = 2'b00,
    SCR1_MEM_WIDTH_HWORD    = 2'b01,
    SCR1_MEM_WIDTH_WORD     = 2'b10,
    SCR1_MEM_WIDTH_DWORD    = 2'b11
`ifdef SCR1_XPROP_EN
    ,
    SCR1_MEM_WIDTH_ERROR    = 'x
`endif // SCR1_XPROP_EN
} type_scr1_mem_width_e;

//-------------------------------------------------------------------------------
// Memory response enum
//-------------------------------------------------------------------------------
typedef enum logic[1:0] {
    SCR1_MEM_RESP_NOTRDY    = 2'b00,
    SCR1_MEM_RESP_RDY_OK    = 2'b01,
    SCR1_MEM_RESP_RDY_ER    = 2'b10
`ifdef SCR1_XPROP_EN
    ,
    SCR1_MEM_RESP_ERROR     = 'x
`endif // SCR1_XPROP_EN
} type_scr1_mem_resp_e;

`endif // SCR1_MEMIF_SVH
