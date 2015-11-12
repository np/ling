-- should be named enum_par
replicate_par = proc(c : {!Int ^ 10})
  c{d}
  slice (d) 10 as i
  send d i
