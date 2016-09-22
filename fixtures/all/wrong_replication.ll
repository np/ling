wrong_replication = \ (n : Int)->
  proc(c : [: ?Bool. !Int ^ n :])
    split c as [: c_ ^ n :].
    let x : Bool <- c_.
    sequence ^ n (c_ <- 42)
