test3 =
  new (c : ?Int. [!Int, !Int], d)
  (
    recv c (x0 : Int)
    c[c0,c1]
    ( send c0 x0 | send c1 x0 )
  |
    send d 1
    d{d0,d1}
    ( recv d0 (y0 : Int) | recv d1 (z0 : Int) )
  ).
