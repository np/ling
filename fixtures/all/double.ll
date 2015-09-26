double (i : ?Int, r : !Int) =
  recv i(xi : Int)
  new (c : ?Int. ?Int. !Int, d)
  (
    recv c(x : Int) recv c(y : Int) send c (x + y)
  |
    send d xi send d xi recv d(z : Int) send r z
  )
