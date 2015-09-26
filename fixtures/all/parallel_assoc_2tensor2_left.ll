parallel_assoc_2tensor2_left (cde : [[!Int, !Int], !Int]) =
  cde[cd,e]
  cd[c,d]
  ( send c 1
  | send d 2
  | send e 3
  )
