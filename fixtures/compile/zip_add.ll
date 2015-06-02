zip_add (xs : {?Int ^ 10}, ys : {?Int ^ 10}, zs : [!Int ^ 10]) =
  xs{x}
  ys{y}
  zs[z]
  slice (x,y,z) 10 as i
  recv x (a : Int)
  recv y (b : Int)
  send z (a + b).
