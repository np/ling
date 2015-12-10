zip_add = proc(xs : {?Int ^ 10}, ys : {?Int ^ 10}, zs : [!Int ^ 10])
  xs{x^10}
  ys{y^10}
  zs[z^10]
  slice (x,y,z) 10 as i
  recv x (a : Int)
  recv y (b : Int)
  send z (a + b)
