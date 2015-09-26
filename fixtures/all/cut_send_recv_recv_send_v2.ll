cut_send_recv_recv_send_v2 = new (c : !Int.?Int, d : ?Int.!Int)
  ( recv d (y : Int)
    send d 2
  | send c 1
    recv c (x : Int)
  )

