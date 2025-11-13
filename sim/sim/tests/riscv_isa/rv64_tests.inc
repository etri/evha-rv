
ARCH_lowercase = $(shell echo $(ARCH) | tr A-Z a-z)

rv64_isa_ui += \
                    isa/rv64ui/add.S		\
                    isa/rv64ui/addi.S		\
                    isa/rv64ui/addiw.S		\
                    isa/rv64ui/addw.S		\
                    isa/rv64ui/and.S		\
                    isa/rv64ui/andi.S		\
                    isa/rv64ui/auipc.S		\
                    isa/rv64ui/beq.S		\
                    isa/rv64ui/bge.S		\
                    isa/rv64ui/bgeu.S		\
                    isa/rv64ui/blt.S		\
                    isa/rv64ui/bltu.S		\
                    isa/rv64ui/bne.S		\
                    isa/rv64ui/fence_i.S	\
                    isa/rv64ui/jal.S		\
                    isa/rv64ui/jalr.S		\
                    isa/rv64ui/lb.S			\
                    isa/rv64ui/lbu.S		\
                    isa/rv64ui/ld.S			\
                    isa/rv64ui/lh.S			\
                    isa/rv64ui/lhu.S		\
                    isa/rv64ui/lui.S		\
                    isa/rv64ui/lw.S			\
                    isa/rv64ui/lwu.S		\
                    isa/rv64ui/or.S			\
                    isa/rv64ui/ori.S		\
                    isa/rv64ui/sb.S			\
                    isa/rv64ui/sd.S			\
                    isa/rv64ui/sh.S			\
                    isa/rv64ui/simple.S		\
                    isa/rv64ui/sll.S		\
                    isa/rv64ui/slli.S		\
                    isa/rv64ui/slliw.S		\
                    isa/rv64ui/sllw.S		\
                    isa/rv64ui/slt.S		\
                    isa/rv64ui/slti.S		\
                    isa/rv64ui/sltiu.S		\
                    isa/rv64ui/sltu.S		\
                    isa/rv64ui/sra.S		\
                    isa/rv64ui/srai.S		\
                    isa/rv64ui/sraiw.S		\
                    isa/rv64ui/sraw.S		\
                    isa/rv64ui/srl.S		\
                    isa/rv64ui/srli.S		\
                    isa/rv64ui/srliw.S		\
                    isa/rv64ui/srlw.S		\
                    isa/rv64ui/sub.S		\
                    isa/rv64ui/subw.S		\
                    isa/rv64ui/sw.S			\
                    isa/rv64ui/xor.S		\
                    isa/rv64ui/xori.S	

rv64_isa_um += \
                    isa/rv64um/div.S       \
                    isa/rv64um/divu.S      \
                    isa/rv64um/divuw.S     \
                    isa/rv64um/divw.S      \
                    isa/rv64um/mul.S       \
                    isa/rv64um/mulh.S      \
                    isa/rv64um/mulhsu.S    \
                    isa/rv64um/mulhu.S     \
                    isa/rv64um/mulw.S      \
                    isa/rv64um/rem.S       \
                    isa/rv64um/remu.S      \
                    isa/rv64um/remuw.S     \
                    isa/rv64um/remw.S      

rv64_isa_uf += \
                    isa/rv64uf/fadd.S       \
                    isa/rv64uf/fclass.S     \
                    isa/rv64uf/fcmp.S       \
                    isa/rv64uf/fcvt.S       \
                    isa/rv64uf/fcvt_w.S     \
                    isa/rv64uf/fdiv.S       \
                    isa/rv64uf/fmadd.S      \
                    isa/rv64uf/fmin.S       \
                    isa/rv64uf/ldst.S       \
                    isa/rv64uf/move.S       \
                    isa/rv64uf/recoding.S  

rv64_isa_ud += \
                    isa/rv64ud/fadd.S		\
                    isa/rv64ud/fclass.S		\
                    isa/rv64ud/fcmp.S		\
                    isa/rv64ud/fcvt.S		\
                    isa/rv64ud/fcvt_w.S		\
                    isa/rv64ud/fdiv.S		\
                    isa/rv64ud/fmadd.S		\
                    isa/rv64ud/fmin.S		\
                    isa/rv64ud/ldst.S		\
                    isa/rv64ud/move.S		\
                    isa/rv64ud/recoding.S	\
                    isa/rv64ud/structural.S	

rv64_isa_ua += \
                    isa/rv64ua/amoadd_d.S	\
                    isa/rv64ua/amoadd_w.S	\
                    isa/rv64ua/amoand_d.S	\
                    isa/rv64ua/amoand_w.S	\
                    isa/rv64ua/amomax_d.S	\
                    isa/rv64ua/amomax_w.S	\
                    isa/rv64ua/amomaxu_d.S	\
                    isa/rv64ua/amomaxu_w.S	\
                    isa/rv64ua/amomin_d.S	\
                    isa/rv64ua/amomin_w.S	\
                    isa/rv64ua/amominu_d.S	\
                    isa/rv64ua/amominu_w.S	\
                    isa/rv64ua/amoor_d.S	\
                    isa/rv64ua/amoor_w.S	\
                    isa/rv64ua/amoswap_d.S	\
                    isa/rv64ua/amoswap_w.S	\
                    isa/rv64ua/amoxor_d.S	\
                    isa/rv64ua/amoxor_w.S	\
                    isa/rv64ua/lrsc.S	

rv64_isa_uc += \
                    isa/rv64uc/rvc.S

rv64_isa_mi += \
                    isa/rv64mi/access.S				\
                    isa/rv64mi/breakpoint.S			\
                    isa/rv64mi/csr.S				\
                    isa/rv64mi/illegal.S			\
                    isa/rv64mi/ld-misaligned.S		\
                    isa/rv64mi/lh-misaligned.S		\
                    isa/rv64mi/lw-misaligned.S		\
                    isa/rv64mi/ma_addr.S			\
                    isa/rv64mi/ma_fetch.S			\
                    isa/rv64mi/mcsr.S				\
                    isa/rv64mi/sbreak.S				\
                    isa/rv64mi/scall.S				\
                    isa/rv64mi/sd-misaligned.S		\
                    isa/rv64mi/sh-misaligned.S		\
                    isa/rv64mi/sw-misaligned.S		\
                    isa/rv64mi/zicntr.S		

rv64_isa_si += \
                    isa/rv64si/csr.S                \
                    isa/rv64si/dirty.S              \
                    isa/rv64si/icache-alias.S       \
                    isa/rv64si/ma_fetch.S           \
                    isa/rv64si/sbreak.S             \
                    isa/rv64si/scall.S              \
                    isa/rv64si/wfi.S


#rv64_isa_tests += $(rv64_isa_ui) 
#rv64_isa_tests += $(rv64_isa_um) 
#rv64_isa_tests += $(rv64_isa_uf) 
#rv64_isa_tests += $(rv64_isa_ud) 
#rv64_isa_tests += $(rv64_isa_ua) 
#rv64_isa_tests += $(rv64_isa_uc) 
#rv64_isa_tests += $(rv64_isa_mi) 
rv64_isa_tests += $(rv64_isa_si)

#rv64_isa_tests += isa/rv64ui/add.S 
#rv64_isa_tests += isa/rv64mi/access.S 
#rv64_isa_tests += isa/rv64si/dirty.S 
#rv64_isa_tests += isa/rv64si/icache-alias.S 
