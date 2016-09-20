replicate =
  \ (A : Type)(n : Int)(x : A)->
  proc(os : [!A ^ n])
    split os as [o^n]
    parallel ^ n (o <- x)
