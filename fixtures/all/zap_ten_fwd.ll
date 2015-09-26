zap_ten_fwd (cf : {(?Int -o ?Int) ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10]) =
  cf{cfi}
  cn{cni}
  co[coi]
  slice (cfi,cni,coi) 10 as i
  cfi{cfii,cfio}
  ( fwd(?Int)(cni,cfii)
  | fwd(?Int)(cfio,coi)
  )

