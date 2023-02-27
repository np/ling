new_fuse1_recv_send_send_recv = proc()
  new/fuse1 [d : ?Int.!Int, c : !Int.?Int]
  ( send c 1
    recv c (x : Int)
  | recv d (y : Int)
    send d 2
  )
