
clear -all

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
check_superlint -extract


