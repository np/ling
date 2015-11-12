replicate =
  \(A : Type)(n : Int)(x : A)->
  proc(os : [!A ^ n])
  os[o]
  slice (o) n as _
  send o x
