-- should be named enum_par
replicate_par = proc(c : {!Int ^ 10})
  split c as {d^10}.
  sequence ^ 10 with i
    d <- i
