-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_seq = proc(cf : {?Int -o ?Int ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  split cf as {cfi^10}.
  split cn as {cni^10}.
  split co as [coi^10].
  sequence ^ 10 (
    split cfi as {cfii,cfio}.
    let x : Int <- cni.
    cfii <- x.
    let y : Int <- cfio.
    coi <- y)
