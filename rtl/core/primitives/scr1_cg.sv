/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// Copyright (c) 2025 ETRI
/// Modifications are provided under GPL-3.0-or-later; redistribution must retain the
/// original BSD notice in accordance with its terms.
/// Author: ETRI
/// Date: 11/11/2025
/// @file       <scr1_cg.sv>
/// @brief      SCR1 clock gate primitive
///

`include "scr1_arch_description.svh"

`ifdef SCR1_CLKCTRL_EN
module scr1_cg (
    input   logic   clk,
    input   logic   clk_en,
    input   logic   test_mode,
    output  logic   clk_out
);

// The code below is a clock gate model for simulation.
// For synthesis, it should be replaced by implementation-specific
// clock gate code.

logic latch_en;

always_latch begin
    if (~clk) begin
        latch_en <= test_mode | clk_en;
    end
end

assign clk_out  = latch_en & clk;

endmodule : scr1_cg

`endif // SCR1_CLKCTRL_EN
