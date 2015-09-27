zap_ten_seq = proc(cf : {(?Int -o ?Int) ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  cf{cfi}
  cn{cni}
  co[coi]
  slice (cfi,cni,coi) 10 as i
  cfi{cfii,cfio}
  recv cni (x : Int)
  send cfii x
  recv cfio (y : Int)
  send coi y

