# Run one of the other jg tcl scripts
# Then run the command: include tcl/my_superlint_tcl.tcl
# OBS.: the enables/disables might be specific to the version of Jasper I'm using
clear -task <embedded>
check_superlint -init
config_rtlds -rule  -enable -category {AUTO_FORMAL_FSM_DEADLOCK_LIVELOCK AUTO_FORMAL_FSM_REACHABILITY} 
config_rtlds -rule  -disable -category {AUTO_FORMAL_BUS AUTO_FORMAL_CASE} 
check_superlint -extract 
check_superlint -prove  -bg