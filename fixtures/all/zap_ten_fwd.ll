-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_fwd = proc(cf : {?Int -o ?Int ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  split cf as {cfi^10}.
  split cn as {cni^10}.
  split co as [coi^10].
  parallel ^ 10 (
    split cfi as {cfii,cfio}.
    ( fwd(?Int)(cni,cfii)
    | fwd(?Int)(cfio,coi)))
