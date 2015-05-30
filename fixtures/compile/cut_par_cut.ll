cut_par_cut =
  ( new (c  : !Int, d  : ?Int) ( send c 1  | recv d  (x  : Int) )
  | new (c' : !Int, d' : ?Int) ( send c' 1 | recv d' (x' : Int) )
  )
.
