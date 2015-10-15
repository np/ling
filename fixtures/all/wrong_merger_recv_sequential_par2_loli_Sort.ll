wrong_merger_send_seqential_par2_loli_Sort =
 \(m : Int)(n : Int)->
 proc( c : {Sort Int m, Sort Int n} -o Sort Int (m + n) )
  c{c01,d}
  c01[c0,c1]
  recv d (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  recv c0 (v0 : Vec Int m).
  recv c1 (v1 : Vec Int n).
  send d (merge m n v0 v1)
