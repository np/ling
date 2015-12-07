new_alloc = proc(c : !Int)
  new/ alloc [d : !Int, e]
  ( send d 1
  | fwd(!Int)(c,e))
