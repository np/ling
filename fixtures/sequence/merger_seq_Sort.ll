m : Int.
n : Int.

merger_seq (c : [Sort Int m, Sort Int n] -o Sort Int (m + n)) =
  c{d,io} d{d0,d1}
  recv io (vi : Vec Int (m + n))
  send d0 (take Int m n vi) -- Since these two sends are on different channels
  send d1 (drop Int m n vi) -- they can commute, thus are actually in parallel
  recv d0 (v0 : Vec Int m)  -- Same here these two recv can commute
  recv d1 (v1 : Vec Int n)
  send io (merge m n v0 v1)
.
