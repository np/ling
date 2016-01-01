new_seq_par_par =
  proc()
  new [: cd: {!Int,!Bool}, ef: {?Int,?Bool} :].
  split cd {c,d}.
  split ef {e,f}.
  c <- 1.
  d <- `true.
  let b : Bool <- f.
  let i : Int  <- e
