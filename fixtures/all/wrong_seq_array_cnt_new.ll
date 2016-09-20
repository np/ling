wrong_seq_array_cnt_new = \(ann : Allocation) -> proc()
  new/ann (c :* Int).
  split c [:d,e:].
  d <- 1.
  e <- 2
