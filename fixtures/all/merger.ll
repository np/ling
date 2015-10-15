-- Should be renamed merge_ParSort_seq_recv
merger =
 \(m : Int)(n : Int)->
 proc( c0 : [! Vec Int m, ? Vec Int m]
     , c1 : [! Vec Int n, ? Vec Int n]
     , ci : ? Vec Int (m + n)
     , co : ! Vec Int (m + n)
     )
  c0[c0i,c0o]
  c1[c1i,c1o]
  recv ci (vi : Vec Int (m + n))
  ( send c0i (take Int m n vi)
  | send c1i (drop Int m n vi)
  | recv c0o (v0 : Vec Int m)
    recv c1o (v1 : Vec Int n)
    send co  (merge m n v0 v1)
  )
