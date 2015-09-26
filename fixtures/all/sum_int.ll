sum_int (a : {?Int ^ 10}, r : !Int) =
  new (itmp : !Int.?Int, tmp)
  (send itmp 0
   fwd(?Int)(itmp, r)
  |
   a{ai}
   slice (ai) 10 as i
   recv ai  (x : Int)
   recv tmp (y : Int)
   send tmp (x + y)
  )

