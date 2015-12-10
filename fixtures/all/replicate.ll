replicate =
  \(A : Type)(n : Int)(x : A)->
  proc(os : [!A ^ n])
  os[o^n]
  slice (o) n as _
    send o x
