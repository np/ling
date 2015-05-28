zap_ten_fwd (cf : {(?Int -o ?Int) ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10]) =
  slice 10 as i
  cf{cfi}
  cn{cni}
  co[coi]
  cfi{cfii,cfio}
  ( fwd (?Int)(cni, cfii)
  | fwd (?Int)(cfio, coi)
  )
.
