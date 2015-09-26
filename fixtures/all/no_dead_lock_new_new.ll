-- Requires a mix
no_dead_lock_new_new =
  new (c : ?Int, d)
  new (e : ?Int, f)
  (
    recv c (x : Int)
    send f x
  |
    send d 5
  |
    recv e (y : Int)
  )
