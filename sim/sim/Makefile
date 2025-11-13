# src_dir := $(dir $(lastword $(MAKEFILE_LIST)))
rtl_src_dir := $(root_dir)/../rtl/
rtl_fpu_files ?= fpnew.files
rtl_core_files ?= core.files
rtl_top_files ?= ahb_top.files
rtl_tb_files ?= ahb_tb.files
rtl_inc_dir ?= $(root_dir)/../rtl/includes
rtl_inc_fpnew_dir ?= $(root_dir)/../rtl/fpnew/include
rtl_inc_tb_dir ?= $(root_dir)/../tb
top_module ?= scr1_top_tb_ahb

rtl_fpu_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_fpu_files)))
rtl_core_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_core_files)))
rtl_top_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_top_files)))
rtl_tb_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_tb_files)))
sv_list := $(rtl_fpu_list) $(rtl_core_list) $(rtl_top_list) $(rtl_tb_list)


.PHONY: build_modelsim build_vcs build_ncsim build_ncsim_wf build_verilator build_verilator_wf

default: build_ncsim

build_modelsim: $(sv_list)
	cd $(bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O1 -mfcu -sv \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+nowarnSVCHK  \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_vcs: $(sv_list)
	cd $(bld_dir); \
	vcs \
	-full64 \
	-lca \
	-sverilog \
	-notice \
	+lint=all,noVCDE,noNS,noVNGS,noSVA-DIU,noSVA-CE,noSVA-NSVU \
	-timescale=1ns/1ps \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_fpnew_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	-nc \
	-debug_all \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_vcs_wf: $(sv_list)
	cd $(bld_dir); \
	vcs \
	-full64 \
	-lca \
	-sverilog \
	-notice \
	+lint=all,noVCDE,noNS,noVNGS,noSVA-DIU,noSVA-CE,noSVA-NSVU \
	-timescale=1ns/1ps \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_fpnew_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+define+VCS_DUMP \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	-nc \
	-debug_access \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

#-P $(VERDI_HOME)/share/PLI/VCS/linux64/novas.tab $(VERDI_HOME)/share/PLI/VCS/linux64/pli.a

build_ncsim: $(sv_list)
	cd $(bld_dir); \
	irun \
	-elaborate \
	-64bit \
	-disable_sem2009 \
	-verbose \
	-timescale 1ns/1ps \
	-incdir $(rtl_inc_dir) \
	-incdir $(rtl_inc_fpnew_dir) \
	-incdir $(rtl_inc_tb_dir) \
	-debug \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-top $(top_module)

build_ncsim_wf: $(sv_list)
	cd $(bld_dir); \
	irun \
	-elaborate \
	-64bit \
	-disable_sem2009 \
	-verbose \
	-timescale 1ns/1ps \
	-incdir $(rtl_inc_dir) \
	-incdir $(rtl_inc_fpnew_dir) \
	-incdir $(rtl_inc_tb_dir) \
	-debug \
	-access \
	+r \
	+define+SCR1_DUMP_WF_NCSIM \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-top $(top_module)

build_verilator: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	+1800-2017ext+sv \
	-Wno-fatal \
	$(VERILATOR_5X_OPTS) \
	--top-module $(top_module) \
	-DSCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	--clk clk \
	--exe $(scr1_wrapper) \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;

build_verilator_wf: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	+1800-2017ext+sv \
	-Wno-fatal \
	$(VERILATOR_5X_OPTS) \
	--top-module $(top_module) \
	-DSCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	-CFLAGS -DVCD_TRACE -CFLAGS -DTRACE_LVLV=20 \
	-CFLAGS -DVCD_FNAME=simx.vcd \
	--clk clk \
	--exe $(scr1_wrapper) \
	--trace \
	--trace-params \
    --trace-structs \
    --trace-underscore \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;


