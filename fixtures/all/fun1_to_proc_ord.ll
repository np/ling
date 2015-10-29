fun1_to_proc_ord =
  \(I O : Type)
   (f : (x : I) -> O)->
  proc(c : [: ?I, !O :])
  c[: i, o :]
  recv i (x : I).
  send o (f x)
