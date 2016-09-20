zip_add = proc(xs : {?Int ^ 10}, ys : {?Int ^ 10}, zs : [!Int ^ 10])
  split xs as {x^10}.
  split ys as {y^10}.
  split zs as [z^10].
  parallel ^ 10 (
    let a : Int <- x.
    let b : Int <- y.
    z <- (a + b))
