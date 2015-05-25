zap_ten_seq (cf : {(?Int -o ?Int) ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10]) =
  slice 10 as i
  cf{cfi}
  cn{cni}
  co[coi]
  cfi{cfii,cfio}
  recv cni (x : Int)
  send cfii x
  recv cfio (y : Int)
  send coi y
.
