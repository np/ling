sqr_dbl = proc(i: ?Int, o: !Int)
  let x : Int <- i.
  new (c: Int).
  c <- (x * x).
  let y : Int <- c.
  o <- (y + y)

