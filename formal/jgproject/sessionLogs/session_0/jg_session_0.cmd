# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2023.09
# platform  : Linux 6.5.0-44-generic
# version   : 2023.09p002 64 bits
# build date: 2023.11.21 13:10:30 UTC
# ----------------------------------------
# started   : 2024-07-31 21:57:09 -03
# hostname  : victorhug-340XAA-350XAA-550XAA.(none)
# pid       : 16493
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:33909' '-style' 'windows' '-data' 'AAAA1HicVY69CsJQFIO/q7iKD9FJ8FJ/Cg4duripRQuuItVNvKWtCC76qL7JNVYKmnASCDkQA8QP7z0NunfJgCUrtiykKTs5BERMmBOSyEPRMmaqs1KrbKZGA/P6OrHhF2bz/HPotcW20tENGXHgLDpu7LlyoZIWoqOk5sRReUqmdp+19mVaUJPr54M3OcAYaQ==' '-proj' '/home/victorhug/Documents/TCC/Código/NES_MiSTerCadence/formal/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/victorhug/Documents/TCC/Código/NES_MiSTerCadence/formal/jgproject/.tmp/.initCmds.tcl' 'NES.tcl'

clear -all

# Load checks that will be verified
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_VHDL.def
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_Verilog_SystemVerilog.def 
#config_rtlds -rule -load Superlint_Deployment_Rulefile_Lint_2022_09_Customer.def


# analyze -register -vhdl -f files_vhd.f
# analyze -sort -vhdl -f files_vhd.f

analyze -vhdl ../rtl/statemanager.vhd
analyze -vhdl ../rtl/bus_savestates.vhd
analyze -vhdl ../rtl/savestates.vhd
analyze -vhdl ../rtl/t65/T65_Pack.vhd
analyze -vhdl ../rtl/t65/T65_MCode.vhd
analyze -vhdl ../rtl/t65/T65_ALU.vhd
analyze -vhdl ../rtl/t65/T65.vhd
analyze -sv ../rtl/regs_savestates.sv


analyze -sv -f files_sv.f
analyze -sv -f files_mappers_sv.f


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
# check_superlint -extract


schematic_viewer -draw -new_window
schematic_viewer -draw -new_window
schematic_viewer -draw -new_window
