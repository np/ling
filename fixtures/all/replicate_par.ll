replicate_par (c : {!Int ^ 10}) =
  c{d}
  slice (d) 10 as i
  send d i
