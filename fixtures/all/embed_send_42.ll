send_42 = proc(c : !Int)
  send c 42

embed_send_42 = proc(c : !Int)
  @send_42(c)
