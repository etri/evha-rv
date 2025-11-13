/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///

`include "scr1_arch_description.svh"

`ifdef SCR1_TCM_EN
module scr1_dp_memory
#(
    parameter SCR1_SIZE     = `SCR1_IMEM_AWIDTH'h00010000,
    parameter SCR1_DWIDTH   = 64,
    parameter SCR1_DBYTES   = SCR1_DWIDTH / 8,
	parameter SCR1_AWIDTH	= 32,
	parameter SCR1_ABYTES	= SCR1_AWIDTH / 8
)
(
    input   logic                           clk,
    // Port A
    input   logic                           rena,
    input   logic [$clog2(SCR1_SIZE)-1:2]   addra,
    output  logic [SCR1_AWIDTH-1:0]         qa,
    // Port B
    input   logic                           renb,
    input   logic                           wenb,
    input   logic [SCR1_DBYTES-1:0]         webb,
    input   logic [$clog2(SCR1_SIZE)-1:3]   addrb,
    input   logic [SCR1_DWIDTH-1:0]         datab,
    output  logic [SCR1_DWIDTH-1:0]         qb
);


localparam int unsigned RAM_SIZE_WORDS = SCR1_SIZE/SCR1_DBYTES;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic  [SCR1_DWIDTH-1:0]  ram_block  [RAM_SIZE_WORDS-1:0];

//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (rena) begin
		case (addra[2])
			1'b0 : qa <= ram_block[addra[$clog2(SCR1_SIZE)-1:3]][31:0];
			1'b1 : qa <= ram_block[addra[$clog2(SCR1_SIZE)-1:3]][63:32];
		endcase
    end
end

//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (wenb) begin
        for (int i=0; i<SCR1_DBYTES; i++) begin
            if (webb[i]) begin
                ram_block[addrb][i*8 +: 8] <= datab[i*8 +: 8];
            end
        end
    end
    if (renb) begin
        qb <= ram_block[addrb];
    end
end

endmodule : scr1_dp_memory

`endif // SCR1_TCM_EN
