/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_pipe_fprf.sv>
/// @brief      Floating-Point Register File (FPRF)
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"

module scr1_pipe_fprf (
    // Common
    input   logic                               rst_n,                      // FPRF reset
    input   logic                               clk,                        // FPRF clock

    // EXU <-> FPRF interface
    input   logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs1_addr_i,        // FPRF rs1 read address
    output  logic [`SCR1_XLEN-1:0]              fprf2exu_rs1_data_o,        // FPRF rs1 read data
    input   logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs2_addr_i,        // FPRF rs2 read address
    output  logic [`SCR1_XLEN-1:0]              fprf2exu_rs2_data_o,        // FPRF rs2 read data
    input   logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rs3_addr_i,        // FPRF rs3 read address
    output  logic [`SCR1_XLEN-1:0]              fprf2exu_rs3_data_o,        // FPRF rs3 read data
    input   logic                               exu2fprf_w_req_i,           // FPRF write request
    input   logic [`SCR1_FPRF_AWIDTH-1:0]       exu2fprf_rd_addr_i,         // FPRF rd write address
    input   logic [`SCR1_XLEN-1:0]              exu2fprf_rd_data_i          // FPRF rd write data
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------

logic                        wr_req_vd;

logic                        rs1_addr_vd;
logic                        rs2_addr_vd;
logic                        rs3_addr_vd;

type_scr1_fprf_v [0:`SCR1_FPRF_SIZE-1]                  fprf_int;

//------------------------------------------------------------------------------
// FPRF control logic
//------------------------------------------------------------------------------

// control signals common for distributed logic and RAM implementations
assign  rs1_addr_vd  =   1'b1;
assign  rs2_addr_vd  =   1'b1;
assign  rs3_addr_vd  =   1'b1;

assign  wr_req_vd  =   exu2fprf_w_req_i;


//------------------------------------------------------------------------------
// distributed logic implementation
//------------------------------------------------------------------------------

// asynchronous read operation
assign  fprf2exu_rs1_data_o = ( rs1_addr_vd ) ? fprf_int[exu2fprf_rs1_addr_i] : '0;
assign  fprf2exu_rs2_data_o = ( rs2_addr_vd ) ? fprf_int[exu2fprf_rs2_addr_i] : '0;
assign  fprf2exu_rs3_data_o = ( rs3_addr_vd ) ? fprf_int[exu2fprf_rs3_addr_i] : '0;

// write operation
always_ff @( posedge clk, negedge rst_n ) begin
    if ( ~rst_n ) begin
        fprf_int <= '{default: '0};
    end else if ( wr_req_vd ) begin
		fprf_int[exu2fprf_rd_addr_i] <= exu2fprf_rd_data_i;
    end
end

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------
`ifdef SCR1_FPRF_RST_EN
SCR1_SVA_FPRF_WRITEX : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2fprf_w_req_i |-> !$isunknown({exu2fprf_rd_addr_i, (|exu2fprf_rd_addr_i ? exu2fprf_rd_data_i : `SCR1_XLEN'd0)})
    ) else $error("FPRF error: unknown values");
`endif // SCR1_FPRF_RST_EN

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_fprf

