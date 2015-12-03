letrecv = proc(c : ?Int.!Int)
  recv c (x : Int).
  let y = (x + x).
  send c y
