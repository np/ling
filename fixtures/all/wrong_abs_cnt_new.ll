wrong_abs_cnt_new = \(ann : Allocation)(S : Session)-> proc(d: S)
  new/ann (c :* Int).
  fwd(S)(d,c)
