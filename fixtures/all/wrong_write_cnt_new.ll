wrong_write_cnt_new = \(ann : Allocation) -> proc()
  new/ann (c :* Int).
  c <- 1.
  c <- 2
