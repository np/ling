dead_lock_tensor2_tensor2 (cd : [?Int, !Int], ef : [?Int, !Int]) =
  cd[c,d] ef[e,f]
  (
    recv c (x : Int)
    send f x
  |
    recv e (y : Int)
    send d y
  ).
