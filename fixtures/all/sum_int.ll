sum_int = proc(a : {?Int ^ 10}, r : !Int)
  new/alloc [itmp : !Int.?Int, tmp]
  ( send itmp 0
    fwd(?Int)(itmp, r)
  | a{ai^10}
    slice (ai) 10 as i
      recv ai  (x : Int)
      recv tmp (y : Int)
      send tmp (x + y))

