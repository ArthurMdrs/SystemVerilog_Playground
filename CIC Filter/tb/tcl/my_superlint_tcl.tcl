config_rtlds -rule  -enable -category {AUTO_FORMAL_FSM_DEADLOCK_LIVELOCK AUTO_FORMAL_FSM_REACHABILITY} 
config_rtlds -rule  -disable -category {AUTO_FORMAL_BUS AUTO_FORMAL_CASE} 
check_superlint -extract 
check_superlint -prove  -bg