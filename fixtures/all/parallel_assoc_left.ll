parallel_assoc_left = proc(c : !Int, d : !Int, e : !Int)
  ( ( send c 1 | send d 2 )
  | send e 3
  )
