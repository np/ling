fwd_send_recv_recv_manually = proc(c : !Int.?Int.?Int, d : ?Int.!Int.!Int)
  recv d (x : Int).
  send c x.
  recv c (y : Int).
  send d y.
  recv c (z : Int).
  send d z
