merger_seq_Sort =
 \(m : Int)(n : Int)->
 proc(c : [DotSort Int m, DotSort Int n] -o DotSort Int (m + n))
  c{d,io} d{d0,d1}
  recv io (vi : Vec Int (m + n)).
  send d0 (take Int m n vi).
  send d1 (drop Int m n vi).
  recv d0 (v0 : Vec Int m).
  recv d1 (v1 : Vec Int n).
  send io (merge m n v0 v1)
