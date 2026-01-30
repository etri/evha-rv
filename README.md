# EVHA-RV: Open-source RISC-V

EVHA-RV is an open-source RISC-V core developed by ETRI. It extends the Syntacore SCR1 core with *64-bit operation (RV64)*, *M/S/U privilege modes*, and optional *FPU* and *MMU* blocks. The project includes testbenches and scripts to run on Synopsys VCS and Cadence Xcelium.

## Key features

* Open-sourced under the *GPL-3.0-or-later* license (see `LICENSE` file)
* RV64I or RV64E ISA base + M, A, F, D, C
* Supports Machine, Supervisor, user privilege modes
* 2-4 stage pipeline + additional FPU, MMU module
* (SCR1) Optional Integrated Programmable Interrupt Controller with 16 IRQ lines
* (SCR1) Optional RISC-V Debug subsystem with JTAG interface
* (SCR1) Optional on-chip Tightly-Coupled Memory
* 64-bit AXI4 external interface
* Written in SystemVerilog
* Verification suite provided

For more information on core architecture, see [SCR1 External Architecture Specification](https://github.com/syntacore/scr1/blob/master/docs/scr1_eas.pdf).

For more information on 64-bit CSR, see [Control and Status Register (CSR)](https://github.com/etri/evha-rv/blob/main/Control%20and%20Status%20Register%20(CSR).pdf).

## Repository contents

|Folder | Description
|------ | -----------
|**tb**                                | **Testbench files**
|**sim**                               | **Tests and scripts for simulation**
|├─ build                              | Output build files
|├─ sim/tests/common                   | Common source files for tests
|├─ sim/tests/riscv_isa                | RISC-V ISA tests platform specific source files
|├─ sim/tests/riscv_compliance         | RISC-V Compliance platform specific source files
|├─ sim/tests/benchmarks/dhrystone21   | Dhrystone 2.1 benchmark source files
|├─ sim/tests/benchmarks/coremark      | EEMBC's CoreMark® benchmark platform specific source files
|├─ sim/tests/isr_sample               | Sample program "Interrupt Service Routine"
|├─ sim/tests/hello                    | Sample program "Hello"
|├─ sim/verilator_wrap                 | (SCR1 legacy; not used/validated in EVHA-RV; compatibility not guaranteed)
|└─ dependencies                       | **Dependent submodules**
|   ├─ riscv-tests                     | Common source files for RISC-V ISA tests
|   ├─ riscv-compliance                | Common source files for RISC-V Compliance tests
|   └─ coremark                        | Common source files for EEMBC's CoreMark® benchmark
|**rtl**                               | **EVHA-RV RTL source**
|├─ includes                           | Header files
|├─ core                               | Core top source files
|├─ top                                | Cluster source files
|└─ fpnew                              | FPnew open-source files

## EVHA-RV source file lists

EVHA-RV source file lists of EVHA-RV can be found in ./src (based on SCR1):

* **core.files**    - all synthesized file sources of EVHA-RV
* **fpnew.files**   - additional FPU file sources (FPnew) of EVHA-RV
* **axi_top.files** - synthesized file sources of AXI cluster
* **axi_tb.files**  - testbench file sources for AXI cluster (for simulation only)

## Simulation quick start guide

The project contains testbenches, test sources and scripts to quickly start the simulation. Before starting the simulation, make sure you have:

* installed RISC-V GCC toolchain,
* installed one of the supported simulators,
* initialized submodules with test sources.

### Requirements

#### Operating system

GCC toolchain and make-scripts are supported by most popular Linux-like operating systems.

To run from Windows you can use an additional compatibility layer, such as WSL or Cygwin.

#### RISC-V GCC toolchain

RISC-V GCC toolchain is required to compile the software. You can use pre-built binaries or build the toolchain from scratch.

Detailed explanations are on [SCR1 project Requirements](https://github.com/syntacore/scr1?tab=readme-ov-file#requirements)


#### HDL simulators

Currently supported simulators:

* Synopsys VCS (last verified version: S-2021.09-1)
* Cadence Xcelium (NCSim) (last verified version: 24.09-s006)

Please note that RTL simulator executables should be on your $PATH variable.

#### Tests preparation

The simulation package includes the following tests:

* **hello** - "Hello" sample program
* **isr_sample** - "Interrupt Service Routine" sample program
* **dhrystone21** - Dhrystone 2.1 benchmark
* **coremark** - EEMBC's CoreMark® benchmark (submodule)

### Running simulation

To build RTL, compile and run tests from the repo root folder you have to invoke Makefile.

Makefile supports:

* choice of simulator (ncsim for Xcelium) - `run_<SIMULATOR> = <run_vcs, run_ncsim>`
* configuration setup - `CFG = <MAX, BASE, MIN, CUSTOM>`,
* tests subset to run - `TARGETS = <hello, riscv_isa, dhrystone21, coremark>`

Examples:
``` sh
    make run_vcs CFG=CUSTOM TARGETS=dhrystone21
    make run_ncsim CFG=CUSTOM TARGETS=coremark
```

Build and run parameters can be configured in the `./Makefile`.

After all the tests have finished, the results can be found in `build/<SIM_CFG>/test_results.txt`.

**IMPORTANT:** To ensure correct rebuild, please clean build directory between simulation runs:
``` sh
    make clean
```

Please refer to the *"Simulation environment"* chapter of the [SCR1 User Manual](https://github.com/syntacore/scr1/blob/master/docs/scr1_um.pdf) for more information on setting up a simulation run.

## Contacts

Report an issue: will be updated

Ask a question: will be updated
