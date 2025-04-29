# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2023.09
# platform  : Linux 5.14.0-503.35.1.el9_5.x86_64
# version   : 2023.09p002 64 bits
# build date: 2023.11.21 13:10:30 UTC
# ----------------------------------------
# started   : 2025-04-28 23:33:09 -03
# hostname  : localhost.localdomain.(none)
# pid       : 13897
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:37039' '-style' 'windows' '-data' 'AAABCHicjY/PCgFRGMV/l+w9gCdQrvFnSpqFjY0wMWUrGVYYMVI2PKo3uY6rKXbO6Tun73Ru3c8A0d05h0f5JqkyZsKcoTRmIYcRIW16BAzkgWhp0dFYqVXWVaP/V8vDPD9OZPiGmT1+HCpFsaiUNHUarNiJGVeWXDhwlh7FjBM5G1LlMYnaNbY+3fs3Taa6KdF/ctba33gB4EcfFQ==' '-proj' '/home/pauloldn/poland/proj/NES_MiSTer/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/pauloldn/poland/proj/NES_MiSTer/jgproject/.tmp/.initCmds.tcl' 'formal/NES.tcl'

clear -all

# Load checks that will be verified
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_VHDL.def
# config_rtlds -rule -load /home/jef/cadence/installs/jasper_2023.09p002/etc/res/rtlds/rules/superlint_Verilog_SystemVerilog.def 
#config_rtlds -rule -load Superlint_Deployment_Rulefile_Lint_2022_09_Customer.def


# analyze -register -vhdl -f files_vhd.f
# analyze -sort -vhdl -f files_vhd.f

analyze -vhdl ../rtl/statemanager.vhd
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
include /home/pauloldn/poland/proj/NES_MiSTer/formal/NES.tcl
