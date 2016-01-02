cut_par_cut = proc()
  ( new [c  : !Int, d  : ?Int]. ( send c  1 | recv d  (x  : Int) )
  | new [c' : !Int, d' : ?Int]. ( send c' 1 | recv d' (x' : Int) )
  )

