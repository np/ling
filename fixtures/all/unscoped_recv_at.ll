unscoped_recv_at = proc(c : ?Int, d : !Int)
  @(proc(c) recv c (x : Int))(c).
  send d x
