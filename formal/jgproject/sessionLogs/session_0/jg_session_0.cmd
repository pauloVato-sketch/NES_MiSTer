# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2023.09
# platform  : Linux 5.14.0-570.23.1.el9_6.x86_64
# version   : 2023.09p002 64 bits
# build date: 2023.11.21 13:10:30 UTC
# ----------------------------------------
# started   : 2025-07-11 16:36:08 -03
# hostname  : localhost.localdomain.(none)
# pid       : 11065
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:38447' '-style' 'windows' '-data' 'AAAA+nicjY+7CsJAFETPGmzF7xCyxBeIpLCxCWrQgK0EtRMjSURIo5/qn6xjJKCdM9wZuJwLuwYI7845anmVosuCJRvmypitGiLGDJgQMFMHsqXPUGOVVruRiOlfVC3z/DSh4Vtm/fhpaDdgg7Q0PXxSTnLGjR1XzhTKi5yRU3LkoH1MIrrDSr9I9IKSvW7eegErBBxX' '-proj' '/home/pauloldn/poland/proj/NES_MiSTer/formal/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/pauloldn/poland/proj/NES_MiSTer/formal/jgproject/.tmp/.initCmds.tcl' 'NES.tcl'

clear -all
# Jasper was complaining that the extraction was happening before the initialization
# and complained about initialization happening without clear -all, so I moved
# the initialization here and no more errors were shown.
check_superlint -init
# Load checks that will be verified
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_VHDL.def
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_Verilog_SystemVerilog.def 
#config_rtlds -rule -load Superlint_Deployment_Rulefile_Lint_2022_09_Customer.def

# analyze -register -vhdl -f files_vhd.f
# analyze -sort -vhdl -f files_vhd.f
puts "Current directory: [pwd]"
set file_path "../rtl/statemanager.vhd"
if {[file exists $file_path]} {
    puts "Found file at: $file_path"
} else {
    puts "ERROR: File $file_path not found!"
    exit 1
}
analyze -vhdl ../rtl/statemanager.vhd
analyze -vhdl ../rtl/bus_savestates.vhd
analyze -vhdl ../rtl/savestates.vhd
analyze -vhdl ../rtl/t65/T65_Pack.vhd
analyze -vhdl ../rtl/t65/T65_MCode.vhd
analyze -vhdl ../rtl/t65/T65_ALU.vhd
analyze -vhdl ../rtl/t65/T65.vhd

analyze -sv ../rtl/regs_savestates.sv
# Adição do macro SVA_ENABLE para os arquivos .sv (que podem conter assertions).
analyze +define+SVA_ENABLE=true -sv -f files_sv.f
analyze -sv -f files_mappers_sv.f

# config_rtlds -report_macros
elaborate -top sys_top -bbox_m DSP48A1 -bbox_m dpram -bbox_m EEPROM_24C0x -bbox_m IIR_filter -bbox_m eseopll -bbox_m altddio_out -bbox_m spram -bbox_m hps_io -bbox_m pll -bbox_m pll_cfg -bbox_m sysmem -bbox_m cyclonev_hps_interface_mpu_general_purpose -bbox_m cyclonev_hps_interface_peripheral_uart -bbox_m sysmem_lite -bbox_m cyclonev_hps_interface_interrupts -bbox_m ddr_svc -bbox_m ascal -bbox_m pll_hdmi_adj -bbox_m pll_cfg_hdmi -bbox_m pll_hdmi -bbox_m cyclonev_hps_interface_peripheral_i2c -bbox_m cyclonev_clkselect -bbox_m pll_audio -bbox_m audio_out -bbox_m cyclonev_hps_interface_peripheral_spi_master -bbox_m alsa

clock FPGA_CLK1_50 -factor 1 -phase 1
clock FPGA_CLK2_50 -factor 1 -phase 1
clock pll_hdmi.outclk_0 -factor 1 -phase 1
clock emu.pll.outclk_0 -factor 1 -phase 1
clock emu.pll.outclk_1 -factor 1 -phase 1
clock sysmem.ram2_clk -factor 1 -phase 1
clock hdmi_clk_sw.outclk -factor 1 -phase 1
clock {emu.hps_io.HPS_BUS[36]} -factor 1 -phase 1
clock emu.hps_io.clk_sys -both_edges -factor 1 -phase 1

#reset -expression ~BTN_RESET;
reset -expression emu.reset_nes;

#clock CLK_50M -factor 1 -phase 1
#clock pll.outclk_1 -factor 1 -phase 1
#clock pll.outclk_0 -factor 1 -phase 1
#clock hps_io.clk_sys -both_edges -factor 1 -phase 1
#reset -none -non_resettable_regs 0;
#reset -expression ~RESET;
#reset -none;

# # Extract properties
check_superlint -extract

# Generate connectivity map
check_conn -reverse -src {sys_top emu video video_mixer video_freak} -dest {sys_top emu video video_mixer video_freak} -force -save_as output_map.csv -load

# Find connectivity between blocks

check_conn -reverse -complexity complex -src {sys_top emu video video_mixer video_freak} -dest {sys_top emu video video_mixer video_freak} -force -save_as complex_output_map.csv -force

# check_conn –prove
check_sec -analyze -spec +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_ALU.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_MCode.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_Pack.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/bus_savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/statemanager.vhd} +define+SVA_ENABLE=true -sv {/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/regs_savestates.sv} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/base_proj/NES_MiSTer/formal/files_mappers_sv.f} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/base_proj/NES_MiSTer/formal/files_sv.f} ;
check_sec -analyze -imp +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/statemanager.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/bus_savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_ALU.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_MCode.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_Pack.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65.vhd} +define+SVA_ENABLE=true -sv {/home/pauloldn/poland/proj/NES_MiSTer/rtl/regs_savestates.sv} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/proj/NES_MiSTer/formal/files_sv.f} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/proj/NES_MiSTer/formal/files_mappers_sv.f} ;
check_sec -elaborate -spec -top sys_top -bbox_m {alsa DSP48A1 dpram EEPROM_24C0x IIR_filter eseopll altddio_out spram hps_io pll pll_cfg sysmem cyclonev_hps_interface_mpu_general_purpose cyclonev_hps_interface_peripheral_uart sysmem_lite cyclonev_hps_interface_interrupts ddr_svc ascal pll_hdmi_adj pll_cfg_hdmi pll_hdmi cyclonev_hps_interface_peripheral_i2c cyclonev_clkselect pll_audio audio_out cyclonev_hps_interface_peripheral_spi_master} ;
check_sec -elaborate -imp -top sys_top -bbox_m {alsa DSP48A1 dpram EEPROM_24C0x IIR_filter eseopll altddio_out spram hps_io pll pll_cfg sysmem cyclonev_hps_interface_mpu_general_purpose cyclonev_hps_interface_peripheral_uart sysmem_lite cyclonev_hps_interface_interrupts ddr_svc ascal pll_hdmi_adj pll_cfg_hdmi pll_hdmi cyclonev_hps_interface_peripheral_i2c cyclonev_clkselect pll_audio audio_out cyclonev_hps_interface_peripheral_spi_master} ;
check_sec -setup ;
check_sec -auto_map_reset_x_values on ;

check_sec -analyze -spec +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_ALU.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_MCode.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65_Pack.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/t65/T65.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/bus_savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/statemanager.vhd} +define+SVA_ENABLE=true -sv {/home/pauloldn/poland/base_proj/NES_MiSTer/rtl/regs_savestates.sv} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/base_proj/NES_MiSTer/formal/files_mappers_sv.f} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/base_proj/NES_MiSTer/formal/files_sv.f} ;
check_sec -analyze -imp +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/statemanager.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/bus_savestates.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_ALU.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_MCode.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65_Pack.vhd} +define+SVA_ENABLE=true -vhdl {work::/home/pauloldn/poland/proj/NES_MiSTer/rtl/t65/T65.vhd} +define+SVA_ENABLE=true -sv {/home/pauloldn/poland/proj/NES_MiSTer/rtl/regs_savestates.sv} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/proj/NES_MiSTer/formal/files_sv.f} +define+SVA_ENABLE=true -sv -f {/home/pauloldn/poland/proj/NES_MiSTer/formal/files_mappers_sv.f} ;
check_sec -elaborate -spec -top  -bbox_m {alsa DSP48A1 dpram EEPROM_24C0x IIR_filter eseopll altddio_out spram hps_io pll pll_cfg sysmem cyclonev_hps_interface_mpu_general_purpose cyclonev_hps_interface_peripheral_uart sysmem_lite cyclonev_hps_interface_interrupts ddr_svc ascal pll_hdmi_adj pll_cfg_hdmi pll_hdmi cyclonev_hps_interface_peripheral_i2c cyclonev_clkselect pll_audio audio_out cyclonev_hps_interface_peripheral_spi_master} ;
check_sec -elaborate -imp -top  -bbox_m {alsa DSP48A1 dpram EEPROM_24C0x IIR_filter eseopll altddio_out spram hps_io pll pll_cfg sysmem cyclonev_hps_interface_mpu_general_purpose cyclonev_hps_interface_peripheral_uart sysmem_lite cyclonev_hps_interface_interrupts ddr_svc ascal pll_hdmi_adj pll_cfg_hdmi pll_hdmi cyclonev_hps_interface_peripheral_i2c cyclonev_clkselect pll_audio audio_out cyclonev_hps_interface_peripheral_spi_master} ;
check_sec -setup ;
check_sec -auto_map_reset_x_values on ;

include /home/pauloldn/poland/proj/NES_MiSTer/formal/SEC.tcl
check_spec
check_sec
check_sec -help
help check_sec -gui
include /home/pauloldn/poland/proj/NES_MiSTer/formal/SEC.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/SEC.tcl
spec_root
print $spec_root
