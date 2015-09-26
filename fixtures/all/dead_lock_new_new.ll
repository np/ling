dead_lock_new_new = proc()
  new (c : ?Int, d)
  new (e : ?Int, f)
  (
    recv c (x : Int)
    send f x
  |
    recv e (y : Int)
    send d y
  )
