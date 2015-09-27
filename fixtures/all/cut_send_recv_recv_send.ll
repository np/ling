cut_send_recv_recv_send = proc() new (c : !Int.?Int, d : ?Int.!Int)
  ( send c 1
    recv c (x : Int)
  | recv d (y : Int)
    send d 2
  )

