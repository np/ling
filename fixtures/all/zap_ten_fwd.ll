-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_fwd = proc(cf : {?Int -o ?Int ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  cf{cfi^10}
  cn{cni^10}
  co[coi^10]
  slice (cfi,cni,coi) 10 as i
  cfi{cfii,cfio}
  ( fwd(?Int)(cni,cfii)
  | fwd(?Int)(cfio,coi)
  )

