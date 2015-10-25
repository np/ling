wrong_par_pat = proc(c : [!Int,?Int])
  c[d,e]
  @(proc (f) fwd 2 (!Int) f){d,e}
