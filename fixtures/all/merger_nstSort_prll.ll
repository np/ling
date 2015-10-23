merger_nstSort_prll =
 \(m : Int)(n : Int)->
 proc( c0 : ~DotSort Int m
     , c1 : ~DotSort Int n
     , c  : DotSort Int (m + n)
     )
  recv c (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  ( recv c0 (v0 : Vec Int m)
  | recv c1 (v1 : Vec Int n)).
  send c (merge m n v0 v1)
