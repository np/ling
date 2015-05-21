zip_add (xs : {?Int ^ 10}, ys : {?Int ^ 10}, zs : [!Int ^ 10]) =
  slice 10 as i
    xs{x}
      ys{y}
        zs[z]
          recv x (a : Int)
          recv y (b : Int)
          send z (a + b).
