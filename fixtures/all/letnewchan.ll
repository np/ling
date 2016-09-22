letnewchan =
  let T = Int in
  proc()
    new [c:?T.!T,d:!T.?T].
    ( let x : T <- c.
      c <- (x + x)
    | d <- 42.
      let y : T <- d)
