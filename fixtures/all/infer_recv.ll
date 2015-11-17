infer_recv = proc(c)
  recv c (x)
  send c (x + x)
