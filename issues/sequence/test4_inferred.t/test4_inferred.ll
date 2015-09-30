test4_inferred = proc(r)
  new (c, d)
  (
    recv c (x0 : Int)
    recv c (x1 : Int)
    recv c (x2 : Int)
    send r (x0 + x1 + x2)
  |
    send d 1
    send d 2
    send d 3
  )
