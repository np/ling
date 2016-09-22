order_LR =
  proc()
    new [: ab : [: !Int, !Int :], cd :].
    split ab as [: a, b :].
    split cd as [: c, d :].
    a <- 1.
    b <- 2.
    let x : Int <- c.
    let y : Int <- d

order_RL =
  proc()
    new [: ba : [: !Int, !Int :], dc :].
    split ba as [: b, a :].
    split dc as [: d, c :].
    b <- 2.
    a <- 1.
    let y : Int <- d.
    let x : Int <- c

-- order_LR_fuse1 == fuse1 order_LR
order_LR_fuse1 =
  proc()
    new [: a : !Int, c :].
    new [: b : !Int, d :].
    a <- 1.
    b <- 2.
    let x : Int <- c.
    let y : Int <- d

-- order_RL_fuse1 == order_LR_fuse1
-- order_RL_fuse1 == fuse1 order_RL
order_RL_fuse1 =
  proc()
    new [: b : !Int, d :].
    new [: a : !Int, c :].
    b <- 2.
    a <- 1.
    let y : Int <- d.
    let x : Int <- c

-- order_LR_fuse2 == fuse2 order_LR
order_LR_fuse2 =
  proc()
    let x : Int = 1.
    let y : Int = 2

-- order_RL_fuse2 == order_LR_fuse2
-- order_RL_fuse2 == fuse2 order_RL
order_RL_fuse2 =
  proc()
    let y : Int = 2.
    let x : Int = 1

-- TODO assert all the equations above.
