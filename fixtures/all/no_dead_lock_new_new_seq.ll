no_dead_lock_new_new_seq = proc()
  new [: d : !Int, c :]
  new [: f : !Int, e :]
  send d 5.
  recv c (x : Int).
  send f x.
  recv e (y : Int)
