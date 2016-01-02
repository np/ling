sqrs_body_session = !Int. ?Int. !Int. ?Int. !Int. ?Int

sqrs_body = \(x: Int)-> proc(c: sqrs_body_session, o: !Int)
  c <- (x * x).
  let x2: Int <- c.
  c <- (x2 * x2).
  let x4: Int <- c.
  c <- (x4 * x4).
  let x8: Int <- c.
  o <- (x8 * x8)

sqrs_main = proc(i: ?Int, o: !Int)
  let x: Int <- i.
  new (c: Int).
  @(sqrs_body x)(c,o)
