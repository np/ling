m : Int.
n : Int.

merger_seq ( c0 : ! Vec Int m. ? Vec Int m
           , c1 : ! Vec Int n. ? Vec Int n
           , ci : ? Vec Int (m + n)
           , co : ! Vec Int (m + n)
           ) =
  recv ci (vi : Vec Int (m + n))
  send c0 (take Int m n vi) -- Since these two sends are on different channels
  send c1 (drop Int m n vi) -- they can commute, thus are actually in parallel
  recv c0 (v0 : Vec Int m)  -- Same here these two recv can commute
  recv c1 (v1 : Vec Int n)
  send co (merge m n v0 v1)
.
