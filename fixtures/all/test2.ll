test2 = proc()
  new (c : {?Int. !Int. ?Int, !Int. ?Int. !Int}, d)
  (
    c{c0,c1}
    recv c0 (x0 : Int)
    send c1 (x0 + 1)
    recv c1 (x1 : Int)
    send c0 (x1 + x0 + 2)
    recv c0 (x2 : Int)
    send c1 (x2 + x1 + x0 + 3)
  | d[d0,d1]
    (
      send d0 1
      recv d0 (y0 : Int)
      send d0 (y0 + 4)
    |
      recv d1 (z0 : Int)
      send d1 (z0 + 5)
      recv d1 (z1 : Int)
    )
  )
