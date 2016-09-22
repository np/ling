-- Use /alloc for this example to be accepted
wrong_new_seq_par_par =
  proc()
  new [: cd: {!Int,!Bool}, ef: {?Int,?Bool} :].
  split cd as {c,d}.
  split ef as {e,f}.
  c <- 1.
  d <- `true.
  let b : Bool <- f.
  let i : Int  <- e
