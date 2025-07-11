# ----------------------------------------------------------------------------
# 0) At the very top, declare your “original” (SPEC) project root:
# ----------------------------------------------------------------------------
set spec_root  /home/pauloldn/poland/base_proj/NES_MiSTer
#————————————————————————————————————————————
# 1) SPEC (original) – VHDL only
#————————————————————————————————————————————
check_sec -analyze -spec +define+SVA_ENABLE=true \
    -vhdl {$spec_root/rtl/statemanager.vhd} \
    -vhdl {$spec_root/rtl/bus_savestates.vhd} \
    -vhdl {$spec_root/rtl/savestates.vhd} \
    -vhdl {$spec_root/rtl/t65/T65_Pack.vhd} \
    -vhdl {$spec_root/rtl/t65/T65_MCode.vhd} \
    -vhdl {$spec_root/rtl/t65/T65_ALU.vhd} \
    -vhdl {$spec_root/rtl/t65/T65.vhd}


#————————————————————————————————————————————
# 2) SPEC (original) – SystemVerilog only
#————————————————————————————————————————————
check_sec -analyze -spec +define+SVA_ENABLE=true \
    -sv   {$spec_root/rtl/regs_savestates.sv} \
    -sv   -f {$spec_root/formal/files_sv.f} \
    -sv   -f {$spec_root/formal/files_mappers_sv.f}


#————————————————————————————————————————————
# 3) IMP (optimized) – VHDL only (relative paths)
#————————————————————————————————————————————
check_sec -analyze -imp +define+SVA_ENABLE=true \
    -vhdl {rtl/statemanager.vhd} \
    -vhdl {rtl/bus_savestates.vhd} \
    -vhdl {rtl/savestates.vhd} \
    -vhdl {rtl/t65/T65_Pack.vhd} \
    -vhdl {rtl/t65/T65_MCode.vhd} \
    -vhdl {rtl/t65/T65_ALU.vhd} \
    -vhdl {rtl/t65/T65.vhd}


#————————————————————————————————————————————
# 4) IMP (optimized) – SystemVerilog only (relative paths)
#————————————————————————————————————————————
check_sec -analyze -imp +define+SVA_ENABLE=true \
    -sv   {rtl/regs_savestates.sv} \
    -sv   -f {formal/files_sv.f} \
    -sv   -f {formal/files_mappers_sv.f}


#————————————————————————————————————————————
# 5) Elaborate SPEC and IMP
#————————————————————————————————————————————
check_sec -elaborate -spec -top T65
check_sec -elaborate -imp  -top T65


#————————————————————————————————————————————
# 6) Setup & Run SEC
#————————————————————————————————————————————
check_sec -setup
check_sec -auto_map_reset_x_values on
check_sec -run -report_dir sec_results
