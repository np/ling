merger_ParSort_full_prll =
 \(m : Int)(n : Int)->
 proc( c0 : ~ParSort Int m
     , c1 : ~ParSort Int n
     , c  : ParSort Int (m + n)
     )
  c0[c0i,c0o]
  c1[c1i,c1o]
  c{ci,co}
  recv ci (vi : Vec Int (m + n)).
  ( send c0i (take Int m n vi)
  | send c1i (drop Int m n vi)
  | ( recv c0o (v0 : Vec Int m)
    | recv c1o (v1 : Vec Int n)).
    send co (merge m n v0 v1))
