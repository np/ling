wrong_repeat_par = proc(c : {!Int})
  parallel ^ 10 with i (
    split c as {d}.
    d <- 1
  )
