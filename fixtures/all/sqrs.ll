sqrs = proc(i: ?Int, o: !Int)
  let x : Int <- i.
  new/alloc (c :* Int).
  c <- (x * x).
  let x2 : Int <- c.
  c <- (x2 * x2).
  let x4 : Int <- c.
  c <- (x4 * x4).
  let x8 : Int <- c.
  o <- (x8 * x8)

