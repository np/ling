letrecv_ann = proc(c : ?Int.!Int)
  recv c (x : Int).
  let y : Int = (x + x).
  send c y
