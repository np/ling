cut_send_recv_recv_send_with_log_prll =
  proc(logc : !String.!String, logd : !String.!String)
  new [c : !Int.?Int, d : ?Int.!Int].
  ( ( send logd "recv d"
    | recv d (y : Int)).
    ( send logd "send d 2"
    | send d 2)
  | ( send logc "send c 1"
    | send c 1).
    ( send logc "recv c"
    | recv c (x : Int)))
