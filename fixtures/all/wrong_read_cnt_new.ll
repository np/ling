wrong_read_cnt_new = \(ann : Allocation) -> proc()
  new/ann (c :* Int).
  let x : Int <- c
