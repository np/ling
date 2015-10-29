merger_seq_inferred =
 \(m n : Int)->
 proc(c0,c1,ci,co)
  recv ci (vi : Vec Int (m + n)).
  send c0 (take Int m n vi).
  send c1 (drop Int m n vi).
  recv c0 (v0 : Vec Int m).
  recv c1 (v1 : Vec Int n).
  send co (merge m n v0 v1)
