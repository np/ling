-- This could be:
--   zip Double Double Double (\(vx vy: Double)-> (a *D vx) +D vy) n
saxpy =
  \ (n : Int)(a : Double)->
  proc(xs:{?Double ^ n}, ys:{?Double ^ n}, rs:[!Double ^ n])
    split xs as {x ^ n}.
    split ys as {y ^ n}.
    split rs as [r ^ n].
    parallel ^ n (
      let vx : Double <- x.
      let vy : Double <- y.
      r <- ((a *D vx) +D vy))
